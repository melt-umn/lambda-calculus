grammar edu:umn:cs:melt:lambdacalc:term_rewriting;
-- Implementation of normalization using term rewriting library/extension

imports silver:rewrite as s;

-- Rewrite rules from Building Interpreters with Rewriting Strategies (Dolstra and Visser 2002)
-- Alternate let-elimination rule from Kiama example (https://github.com/inkytonik/kiama/blob/master/extras/src/test/scala/org/bitbucket/inkytonik/kiama/example/lambda/Lambda.scala)

-- Alpha renaming with explicit substitution (for reference, not used here)
global alpha::s:Strategy =
  rule on Term of
  | abs(x, e) -> let y::String = freshVar() in abs(y, letT(x, var(y), e)) end
  end;

-- Beta reduction with explicit substitution
global beta::s:Strategy =
  rule on Term of
  | app(abs(x, e1), e2) -> letT(x, e2, e1)
  end;

-- Eta reduction (for reference, not used here)
global eta::s:Strategy =
  rule on Term of
  | abs(x, app(e, var(y)))
    when x == y && !containsBy(eqString, x, e.freeVars) -> e
  end;

-- Let distribution
global letDist::s:Strategy =
  rule on Term of
  | letT(x, e, var(y)) when x == y -> e
  | letT(x, e, var(y)) -> var(y)
  | letT(x, e0, app(e1, e2)) -> app(letT(x, e0, e1), letT(x, e0, e2))
  --| letT(x, e1, abs(y, e2)) when x == y -> abs(x, e2) -- Let-elimination from Stratego example
  | letT(x, e1, abs(y, e2)) ->
    let z::String = freshVar() in abs(z, letT(x, e1, letT(y, var(z), e2))) end
  | letT(x, _, e) when !containsBy(eqString, x, e.freeVars) -> e -- Let-elimination rule from Kiama example
  end;

-- Full eager evaluation, including reduction inside lambdas
global evalInnermost::s:Strategy =
  s:innermost(beta <+ letDist);
global evalOutermost::s:Strategy =
  s:outermost(beta <+ letDist);

-- Eager evaluation (call by value)
global evalEager::s:Strategy =
  s:try(traverse app(evalEager, evalEager) <+ traverse letT(_, evalEager, evalEager)) <*
  s:try((beta <+ letDist) <* evalEager);

-- Lazy evaluation without memoization (call by name)
global evalLazy::s:Strategy =
  s:try(traverse app(evalLazy, _) <+ traverse letT(_, _, evalLazy)) <*
  s:try((beta <+ letDist) <* evalLazy);

global eval::s:Strategy = evalInnermost;

function evaluate
Term ::= t::Term
{
  return
    case s:rewriteWith(eval, new(t)) of
    | just(t1) -> t1
    | nothing() -> error("Rewriting failed")
    end;
}

-- Helper strategy for debugging or visualizing the rewriting process
global printCurrentTerm::s:Strategy =
  rule on Term of
  | t -> unsafeTraceT(t, printT(showDoc(80, t.pp) ++ "\n", unsafeIOT()))
  end;
