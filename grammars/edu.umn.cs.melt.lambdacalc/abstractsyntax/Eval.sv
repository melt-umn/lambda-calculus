grammar edu:umn:cs:melt:lambdacalc:abstractsyntax;

function evaluate
Term ::= t::Term
{
  -- Strategy attributes
  return t.eval;
  
  -- Term rewriting
  {-return
    case rewriteWith(eval, new(t)) of
    | just(t1) -> t1
    | nothing() -> error("Rewriting failed")
    end;-}
}

-- Helper function
function freshVar
String ::=
{
  return "a" ++ toString(genInt());
}
