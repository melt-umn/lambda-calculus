grammar edu:umn:cs:melt:lambdacalc:abstractsyntax;
-- Implementation of normalization using strategy attributes

import core:monad;

-- Rewrite rules from Building Interpreters with Rewriting Strategies (Dolstra and Visser 2002)

-- Alpha renaming with explicit substitution (for reference, not used here)
strategy attribute alpha =
  rule on Term of
  | abs(x, e) -> let y::String = freshVar() in abs(y, letT(x, var(y), e)) end
  end;

-- Beta reduction with explicit substitution
strategy attribute beta =
  rule on Term of
  | app(abs(x, e1), e2) -> letT(x, e2, e1)
  end;

-- Eta reduction (for reference, not used here)
strategy attribute eta =
  rule on Term of
  | abs(x, app(e, var(y)))
    when x == y && !containsBy(stringEq, x, e.freeVars) -> e
  end;

-- Let distribution
strategy attribute letDist =
  rule on Term of
  | letT(x, e, var(y)) when x == y -> e
  | letT(x, e, var(y)) -> var(y)
  | letT(x, e0, app(e1, e2)) -> app(letT(x, e0, e1), letT(x, e0, e2))
  | letT(x, e1, abs(y, e2)) when x == y -> abs(x, e2)
  | letT(x, e1, abs(y, e2)) ->
    let z::String = freshVar() in abs(z, letT(x, e1, letT(y, var(z), e2))) end
  end;

-- Full eager evaluation, including reduction inside lambdas
strategy attribute evalInnermost =
  innermost(beta <+ letDist);

-- Eager evaluation (call by value)
strategy attribute evalEager =
  try(app(evalEager, evalEager) <+ letT(id, evalEager, evalEager)) <*
  try((beta <+ letDist) <* evalEager);

-- Lazy evaluation without memoization (call by name)
strategy attribute evalLazy =
  try(app(evalLazy, id) <+ letT(id, id, evalLazy)) <*
  try((beta <+ letDist) <* evalLazy);

-- Fully expand all remaining lets, for clarity
strategy attribute elimLets = innermost(letDist);

strategy attribute eval = evalInnermost <* elimLets;

attribute alpha, beta, eta, letDist, evalInnermost, evalEager, evalLazy, elimLets, eval occurs on Term;
propagate alpha, beta, eta, letDist, evalInnermost, evalEager, evalLazy, elimLets, eval on Term;

-- Helper strategy for debugging or visualizing the rewriting process
strategy attribute printCurrentTerm =
  rule on Term of
  | t -> unsafeTrace(t, print(show(80, t.pp) ++ "\n", unsafeIO()))
  end;
attribute printCurrentTerm occurs on Term;
propagate printCurrentTerm on Term;
