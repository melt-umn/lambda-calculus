grammar edu:umn:cs:melt:lambdacalc:strategy_attributes;
-- Implementation of normalization using strategy attributes

-- Rewrite rules from Building Interpreters with Rewriting Strategies (Dolstra and Visser 2002)
-- Alternate let-elimination rule from Kiama example (https://github.com/inkytonik/kiama/blob/master/extras/src/test/scala/org/bitbucket/inkytonik/kiama/example/lambda/Lambda.scala)

-- Alpha renaming with explicit substitution (for reference, not used here)
partial strategy attribute alpha =
  rule on Term of
  | abs(x, e) -> let y::String = freshVar() in abs(y, letT(x, var(y), e)) end
  end;

-- Beta reduction with explicit substitution
partial strategy attribute beta =
  rule on Term of
  | app(abs(x, e1), e2) -> letT(x, e2, e1)
  end;

-- Eta reduction (for reference, not used here)
partial strategy attribute eta =
  rule on Term of
  | abs(x, app(e, var(y)))
    when x == y && !contains(x, e.freeVars) -> e
  end;

-- Let distribution
partial strategy attribute letDist =
  rule on Term of
  | letT(x, e, var(y)) when x == y -> e
  | letT(x, e, var(y)) -> var(y)
  | letT(x, e0, app(e1, e2)) -> app(letT(x, e0, e1), letT(x, e0, e2))
  --| letT(x, e1, abs(y, e2)) when x == y -> abs(x, e2) -- Stratego version
  | letT(x, e1, abs(y, e2)) ->
    let z::String = freshVar() in abs(z, letT(x, e1, letT(y, var(z), e2))) end
  | letT(x, _, e) when !contains(x, e.freeVars) -> e -- Kiama version
  end;

-- Full eager evaluation, including reduction inside lambdas
strategy attribute evalInnermost =
  innermost(beta <+ letDist);
strategy attribute evalOutermost =
  outermost(beta <+ letDist);

-- Eager evaluation (call by value)
strategy attribute evalEager =
  try(app(evalEager, evalEager) <+ letT(id, evalEager, evalEager)) <*
  try((beta <+ letDist) <* evalEager);

-- Lazy evaluation without memoization (call by name)
strategy attribute evalLazy =
  try(app(evalLazy, id) <+ letT(id, id, evalLazy)) <*
  try((beta <+ letDist) <* evalLazy);

strategy attribute eval = evalInnermost;

attribute alpha, beta, eta, letDist, evalInnermost, evalOutermost, evalEager, evalLazy, eval occurs on Term;
propagate alpha, beta, eta, letDist, evalInnermost, evalOutermost, evalEager, evalLazy, eval on Term;

function evaluate
Term ::= t::Term
{
  return t.eval;
}

-- Helper strategy for debugging or visualizing the rewriting process
partial strategy attribute printCurrentTerm =
  rule on Term of
  | t -> unsafeTrace(t, print(show(80, t.pp) ++ "\n", unsafeIO()))
  end;
attribute printCurrentTerm occurs on Term;
propagate printCurrentTerm on Term;
