grammar edu:umn:cs:melt:lambdacalc:abstractsyntax;

function evaluate
Term ::= t::Term
{
  local res::Maybe<Term> =
    t.eval;
    --rewriteWith(eval, new(t));
  return
    case res of
    | just(t1) -> t1
    | nothing() -> error("Rewriting failed")
    end;
}

-- Helper function
function freshVar
String ::=
{
  return "a" ++ toString(genInt());
}
