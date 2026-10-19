local frag = require("./frag")
local state = require("./state")
local shared = require("./shared")

local M = {}

local vSymbol = 0
local inPred = VPredicate:new("in", 2)

local terms: FragMap<{[number]: VFunction}> = FragMap:new()
function termCacheGet(term: Frag, arity: number): VFunction
    local arities = terms:get(term.formal)
    if arities ~= nil and arities[arity] ~= nil then
        return arities[arity]
    else
        local fn = VFunction:new(`t{vSymbol}`, arity)
        vSymbol += 1
        if arities ~= nil then
            arities[arity] = fn
        else
            terms:set(term.formal, {[arity] = fn})
        end
        return fn
    end
end

local compTerms: FragMap<VFunction> = FragMap:new()
function compTermCacheGet(pred: Frag, arity: number): VFunction
    local cached = compTerms:get(pred.formal)
    if cached ~= nil then
        return cached
    end

    local fn = VFunction:new(`c{vSymbol}`, arity)
    vSymbol += 1

    compTerms:set(pred.formal, fn)
    return fn
end

local predicates: FragMap<{[number]: VPredicate}> = FragMap:new()
function predCacheGet(pred: Frag, arity: number): VPredicate
    local arities = predicates:get(pred.formal)
    if arities ~= nil and arities[arity] ~= nil then
        return arities[arity]
    else
        local p = VPredicate:new(`p{vSymbol}`, arity)
        vSymbol += 1
        if arities ~= nil then
            arities[arity] = p
        else
            predicates:set(pred.formal, {[arity] = p})
        end
        return p
    end
end

type CompPredInfo = {
    fn: VFunction,
    fnArity: number,
}

type ConversionCtx = {
    termHoles: {VTerm},
    bindingsStack: {number},
    nextFree: number,
    boundedCompPreds: FragMap<CompPredInfo>,
}

function newCtx(boundedCompPreds: FragMap<CompPredInfo>): ConversionCtx 
    return {
        termHoles = {},
        bindingsStack = {},
        nextFree = 0,
        boundedCompPreds = boundedCompPreds,
    }
end

function termToV(term: Frag, bindings: ConversionCtx): VTerm?
    -- If there are more free variables then binding we have a problem
    if not (term.unclosedCount <= #bindings.bindingsStack) then
        -- log(tostring(term), term.unclosedCount, #bindings.bindingsStack, term.cat.name)
        -- assert(false)
        return nil
    end

    -- Terms can contain sentences so we might encounter them in our recursion.
    -- But we don't handle them so just return nil.
    if term.cat ~= shared.termCat then
        return nil
    end

    term = frag.reduceTop(term)
    term = term:changeBinderNames({})

    -- Check specifically for bounded comprehension
    local match = term:match(shared.boundedComprehensionPattern)
    if match ~= nil then
        -- instantiate all the variables in the predicate. the first variable
        -- will be the x in {x ∈ X | p(x)}. The remaining variables should come
        -- from whatever is in bindings
        local holes = {}
        local holeCount = match[1].unclosedCount
        for holeIdx = 0, holeCount - 1 do
            table.insert(holes, Frag:hole(shared.termCat, holeIdx))
        end 
        local prop = match[1]:instantiateVars(holes)

        -- count the number of external variables in the predicate
        local externalArgCount = holeCount - 1
        if holeCount == 0 then externalArgCount = 0 end
        -- then add 1 for the set the comprehension is bounded over
        externalArgCount += 1

        local bound = termToV(match[0], bindings)
        if bound == nil then return nil end

        -- the first argument to the term is the bound
        local args = {bound}
        -- skip the first binding because it is the inner variable
        for bindingIdx = 1, externalArgCount - 1 do
            local varIdx = bindings.bindingsStack[#bindings.bindingsStack + 1 - bindingIdx]
            table.insert(args, VTerm:newVar(varIdx))
        end

        local fn = compTermCacheGet(prop, externalArgCount)
        bindings.boundedCompPreds:set(prop, { fn = fn, fnArity = externalArgCount })

        return fn:with(args)
    end

    if term.formal.varIdx ~= nil then
        -- This is a variable, so return from the bindings stack.
        local vVar = bindings.bindingsStack[#bindings.bindingsStack - term.formal.varIdx]
        return VTerm:newVar(vVar)
    elseif term.formal.holeIdx ~= nil then
        return bindings.termHoles[term.formal.holeIdx]
    elseif term.replacement and term.replacement.unclosedCount ~= 0 then
        -- This is notation that contains a variable. TODO: handle
        assert(false)
    end

    -- First we attempt to convert all the children to terms. If we can then
    -- we treat this term as a function for Vampire.
    local children = {}
    for i, child in term.children do
        local vChild = termToV(child, bindings)
        if vChild == nil then children = nil; break end
        children[i] = vChild
    end

    -- If we didn't manage to convert all the children, e.g. if some of the
    -- children are sentences, then we just convert the whole term to a constant
    -- for Vampire.
    if children == nil then
        -- TODO: if the term is unclosed or has template vars we need to make
        -- this a function and not a constant. For now we just return nil if
        -- unclosed. But we also need to be checking for template vars.
        if term.unclosedCount ~= 0 then
            return nil
        end

        local constant = termCacheGet(term, 0)
        return constant:with({})
    end

    -- Now we can make a new function symbol
    if term.replacement then
        return termCacheGet(term.replacement, #children):with(children)
    end
    if term.formal.templateIdx ~= nil then
        -- Convert all the children into terms
        local children = {}
        for i, child in term.formal.children do
            local vChild = termToV(child, bindings)
            if vChild == nil then return nil end
            children[i] = vChild
        end
        local idx = term.formal.templateIdx
        local vTerm = VFunction:new(`temp{idx}`, #children)
        return vTerm:with(children)
    end
    return nil
end

function predToV(pred: Frag, bindings: ConversionCtx): VFormula?
    pred = frag.reduceTop(pred)
    pred = pred:changeBinderNames({})

    local match = pred:match(shared.impPattern)
    if match ~= nil then
        local lhs = predToV(match[0], bindings)
        local rhs = predToV(match[1], bindings)
        if not lhs or not rhs then return nil end

        return VFormula:newImp(lhs, rhs)
    end
    
    match = pred:match(shared.iffPattern)
    if match ~= nil then
        local lhs = predToV(match[0], bindings)
        local rhs = predToV(match[1], bindings)
        if not lhs or not rhs then return nil end

        return VFormula:newIff(lhs, rhs)
    end

    if pred.formal == shared.falsum.formal then
        return VFormula:newFalse()
    end

    match = pred:match(shared.forallPattern)
    if match ~= nil then
        -- claim the next free variable.
        local var = bindings.nextFree
        bindings.nextFree += 1

        -- push it to the stack before parsing child
        bindings.bindingsStack[#bindings.bindingsStack + 1] = var
        local p = predToV(match[0], bindings)

        -- now pop from the stack
        bindings.bindingsStack[#bindings.bindingsStack] = nil

        if not p then return nil end

        return VFormula:newForall(var, p)
    end

    match = pred:match(shared.existsPattern)
    if match ~= nil then
        local var = bindings.nextFree
        bindings.nextFree += 1
        bindings.bindingsStack[#bindings.bindingsStack + 1] = var
        local p = predToV(match[0], bindings)
        bindings.bindingsStack[#bindings.bindingsStack] = nil

        if not p then return nil end

        return VFormula:newExists(var, p)
    end

    match = pred:match(shared.andPattern)
    if match ~= nil then
        local lhs = predToV(match[0], bindings)
        local rhs = predToV(match[1], bindings)
        if not lhs or not rhs then return nil end

        return VFormula:newAnd(lhs, rhs)
    end

    match = pred:match(shared.orPattern)
    if match ~= nil then
        local lhs = predToV(match[0], bindings)
        local rhs = predToV(match[1], bindings)
        if not lhs or not rhs then return nil end

        return VFormula:newOr(lhs, rhs)
    end

    match = pred:match(shared.notPattern)
    if match ~= nil then
        local p = predToV(match[0], bindings)
        if not p then return nil end

        return VFormula:newNot(p)
    end

    match = pred:match(shared.eqPattern)
    if match ~= nil then
        local lhs = termToV(match[0], bindings)
        local rhs = termToV(match[1], bindings)
        if not lhs or not rhs then return nil end

        return VFormula:newEq(lhs, rhs)
    end

    match = pred:match(shared.inPattern)
    if match ~= nil then
        local lhs = termToV(match[0], bindings)
        local rhs = termToV(match[1], bindings)
        if not lhs or not rhs then return nil end

        return inPred:with({lhs, rhs})
    end

    if pred.formal.templateIdx ~= nil then
        -- Convert all the children into terms. We iterate the presentation
        -- children rather than `pred.formal.children` so that notation like
        -- `succ(n)` is still visible: termToV can only abstract a fully
        -- unfolded term (e.g. the raw iota expression succ reduces to) when it
        -- is closed, so stripping the notation loses arguments that mention
        -- bound variables.
        local children = {}
        for i, child in pred.children do
            local vChild = termToV(child, bindings)
            if vChild == nil then return nil end
            children[i] = vChild
        end

        local idx = pred.formal.templateIdx
        local vPred = VPredicate:new(`temp{idx}`, #children)
        return vPred:with(children)
    end

    -- If we didn't match any of those patterns then we can try and turn this
    -- into a new predicate symbol for vampire.

    -- Convert all the children into terms
    local children = {}
    for i, child in pred.children do
        local vChild = termToV(child, bindings)
        -- if we couldn't turn the child into a term, just give up.
        if vChild == nil then 
            return nil 
        end
        children[i] = vChild
    end

    if pred.replacement then
        if pred.replacement.unclosedCount ~= 0 then assert(false) end
        return predCacheGet(pred.replacement, #children):with(children)
    else
        assert(false)
    end
end

function addCompPred(pred: Frag, info: CompPredInfo, problem: VProblem)
    -- we need one forall variable for the bound and then one forall variable
    -- for each external argument to the predicate. We want to encode:
    -- ∀X ∀a₁ ... ∀aₙ ∀x, x ∈ t(X, a₁, ..., aₙ) ↔ (x ∈ X ∧ p(x, a₁, ..., aₙ))

    -- we take the next index for the extensionality variable.
    local extVarIdx = info.fnArity
    local extVar = VTerm:newVar(extVarIdx)

    local args = {}
    for varI = 0, info.fnArity - 1 do
        table.insert(args, VTerm:newVar(varI))
    end

    local instantiatedFn = info.fn:with(args)

    -- convert the predicate to vampire. TODO: for now don't recursively
    -- collect predicates.
    local ctx = newCtx(FragMap:new())
    args[0] = extVar
    ctx.termHoles = args
    ctx.nextFree = extVarIdx + 1
    local vPred = predToV(pred, ctx)
    if vPred == nil then return end

    local iff = VFormula:newIff(
        inPred:with({extVar, instantiatedFn}), 
        VFormula:newAnd(inPred:with({extVar, VTerm:newVar(0)}), vPred)
    )

    local final = VFormula:newForall(extVarIdx, iff)
    for varI = info.fnArity - 1, 0, -1 do
        final = VFormula:newForall(varI, final)
    end

    problem:addAxiom(final)
end

local options = VOptions:new()
options:setTimeout(50)

export type VampError =
    | { err: "couldnt_convert_frag", frag: Frag }
    | { err: "unprovable" }
    | { err: "could_not_find_proof" }

export type VampInfo = {
    usesGoal: boolean,
    unusedGivens: {Given},
}

export type Given = {
    frag: Frag,
    span: Span
}

function M.handleVampire(state: state.State, givens: {Given}?): (state.State, VampInfo?, VampError?)
    local problem = VProblem:new(options)
    local fail = nil

    local compPreds = FragMap:new()

    -- Conjecture the goal from the knowns
    local conjecture = predToV(state.goal, newCtx(compPreds))
    if conjecture then
        local negConjecture = VFormula:newNot(conjecture :: VFormula)
        problem:addAxiom(negConjecture)
    else
        fail = state.goal
    end

    -- Collect all the knowns as axioms for vampire
    for _, fact in state.knowns :: {[Fact]: Fact} do
        -- Ignore assumptions for now. We could handle later but not really important.
        if fact.assumption ~= nil then continue end

        local vPred = predToV(fact.conclusion, newCtx(compPreds))
        if vPred then problem:addAxiom(vPred) else fail = fact.conclusion end
    end

    -- Add the bounded comprehension definition for each bounded comprehension
    -- we encountered.
    local hasComp = false
    for comp, info in compPreds :: {[Frag]: CompPredInfo} do
        hasComp = true
        addCompPred(comp, info, problem)
    end

    if hasComp then
        local ext = predToV(shared.extensionalityThm.conclusion, newCtx(compPreds))
        assert(ext ~= nil)
        problem:addAxiom(ext)
    end

    -- If any of the Vampire conversions failed report that as the error.
    if fail ~= nil then
        return state:error(), nil, { err = "couldnt_convert_frag", frag = fail }
    end

    local proof, reason = problem:solve()

    -- Check if Vampire was able to prove the conjecture
    if proof == nil then
        log(tostring(problem))
        if reason == "unprovable" then
            return state:error(), nil, { err = "unprovable" }
        else
            return state:error(), nil, { err = "could_not_find_proof" }
        end
    end

    local usesGoal = false
    local proofConclusions: {VFormula} = {}
    for i = 0, proof.stepCount-1 do
        table.insert(proofConclusions, proof:getStep(i).conclusion)
    end

    if state.goal.formal == shared.falsum.formal then
        usesGoal = true
    else
        local negConjecture = VFormula:newNot(conjecture :: VFormula)
        for _, conclusion in proofConclusions do
            if conclusion == negConjecture then
                usesGoal = true
                break
            end
        end
    end

    -- Determine which givens were unused in the proof
    local unusedGivens: {Given} = {}
    if givens then
        for i, given in givens do
            local vf = predToV(given.frag, newCtx(compPreds))
            assert(vf ~= nil)
            local used = false
            for _, conclusion in proofConclusions do
                if conclusion == vf then
                    used = true
                    break
                end
            end
            if not used then
                table.insert(unusedGivens, given)
            end
        end
    end

    -- Success! We proved the goal
    state.knowns:set(state.goal.formal:fact(), state.goal:fact())
    state.info = state.info:withDeduce(state.goal:fact())

    -- TODO: convert vampire proof to formal proof
    state.formal = state.formal:applyTodo(state.goal, "vampire")

    return state, {usesGoal = usesGoal, unusedGivens = unusedGivens}, nil
end

function M.vampErrToDiag(err: VampError, span: Span): Diagnostic
    if err.err == "couldnt_convert_frag" then
        return Diagnostic:new(`Unable to convert \`{err.frag}\` to Vampire`, span:label(""))
    elseif err.err == "unprovable" then
        return Diagnostic:new("Vampire proved the knowns facts do not imply the goal", span:label(""))
    elseif err.err == "could_not_find_proof" then
        return Diagnostic:new("Vampire was unable to prove the goal", span:label(""))
    else
        assert(false)
    end
end

function M.unusedGivenToDiag(given: Given): Diagnostic
    return Diagnostic:newWarning(`unused given \`{given.frag}\``, given.span:labelWarning(""))     
end

function M.readSentenceList(sentences: SentenceList?): {UnResFrag}
    local list = {}
    if sentences == nil then return list end

    while true do
        local s = sentences.sentence
        table.insert(list, s)

        if sentences._rule == "sentence_list.many" then
            sentences = sentences.rest
        else
            break
        end
    end

    return list
end

function M.handleVampireTactic(
    tactic: { _span: Span, sentences: SentenceList? },
    state: state.State
): state.State
    local unGivens = M.readSentenceList(tactic.sentences)
    local givens = {}

    for _, given in unGivens do
        local g, d = given:resolve(state.scope)
        if d ~= nil then d:withTacticInfo(state.info):report() end
        if g == nil then return state:error() end

        -- if we already have the given directly we can move on
        if state.knowns:get(g.formal:fact()) ~= nil then
            continue
        end

        -- otherwise try to get vampire to prove it
        local subState = state:copy()
        subState.goal = g
        subState.info = subState.info:withGoal(g)
        local vState, _, err = M.handleVampire(subState)

        if err ~= nil then
            Diagnostic:new("given fact is not known", given.span:label(""))
                :withTacticInfo(state.info)
                :report()
            return state:error()
        end

        state.knowns:set(g.formal:fact(), g:fact())
        state.formal = vState.formal
        table.insert(givens, {frag = g, span = given.span})
    end
    
    local newState, info, err = M.handleVampire(state:copy(), givens)

    if err then
        M.vampErrToDiag(err, tactic._span)
            :withTacticInfo(state.info)
            :report()
    end

    if info and not info.usesGoal then
        Diagnostic:newWarning("Vampire proved a contradiction, not the goal", tactic._span:labelWarning(""))
            :withTacticInfo(state.info)
            :report()
    end

    if info and #info.unusedGivens > 0 then
        for _, given in info.unusedGivens do
            M.unusedGivenToDiag(given)
                :withTacticInfo(state.info)
                :report()
        end
    end

    return newState
end

return M