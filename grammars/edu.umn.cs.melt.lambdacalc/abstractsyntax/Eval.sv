grammar edu:umn:cs:melt:lambdacalc:abstractsyntax;

imports silver:rewrite as s;

-- Rewrite rules from Building Interpreters with Rewriting Strategies (Dolstra and Visser 2002)

-- Alpha reduction with explicit substitution (for reference, not used here)
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
    when x == y && !containsBy(stringEq, x, e.freeVars) -> e
  end;

-- Let distribution
global subsVar::s:Strategy =
  rule on Term of
  | letT(x, e, var(y)) when x == y -> e
  | letT(x, e, var(y)) -> var(y)
  end;

global subsApp::s:Strategy =
  rule on Term of
  | letT(x, e0, app(e1, e2)) -> app(letT(x, e0, e1), letT(x, e0, e2))
  end;

global subsAbs::s:Strategy =
  rule on Term of
  | letT(x, e1, abs(y, e2)) when x == y -> abs(x, e2)
  | letT(x, e1, abs(y, e2)) ->
    let z::String = freshVar() in abs(z, letT(x, e1, letT(y, var(z), e2))) end
  end;

-- Full eager evaluation, including reduction inside lambdas
global evalInnermost::s:Strategy =
  s:innermost(beta <+ subsVar <+ subsApp <+ subsAbs);

-- Eager evaluation (call by value)
global evalEager::s:Strategy =
  s:try(traverse app(evalEager, evalEager) <+ traverse letT(_, evalEager, evalEager)) <*
  s:try((beta <+ subsVar <+ subsApp <+ subsAbs) <* evalEager);

-- Lazy evaluation without memoization (call by name)
global evalLazy::s:Strategy =
  s:try(traverse app(evalLazy, _) <+ traverse letT(_, _, evalLazy)) <*
  s:try((beta <+ subsVar <+ subsApp <+ subsAbs) <* evalLazy);

-- Fully expand all remaining lets, for clarity
global expandSubs::s:Strategy =
  s:innermost(subsVar <+ subsApp <+ subsAbs);

global eval::s:Strategy = evalInnermost <* expandSubs;

-- Helper functions
function evaluate
Term ::= t::Term
{
  return
    case rewriteWith(eval, new(t)) of
    | just(t1) -> t1
    | nothing() -> error("Rewriting failed")
    end;
}

function freshVar
String ::=
{
  return "a" ++ toString(genInt());
}

-- Helper strategy for debugging or visualizing the rewriting process
global printCurrentTerm::s:Strategy =
  rule on Term of
  | t -> unsafeTrace(t, print(show(80, t.pp) ++ "\n", unsafeIO()))
  end;
