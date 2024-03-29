grammar edu:umn:cs:melt:lambdacalc:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;

synthesized attribute freeVars::[String];

nonterminal Term with pp, freeVars;

abstract production var
top::Term ::= id::String
{
  top.pp = text(id);
  top.freeVars = [id];
}

abstract production abs
top::Term ::= id::String body::Term
{
  local unfolded::([String], Term) = unfoldAbsVars(top);
  top.pp = pp"\${ppImplode(space(), map(text, unfolded.fst))}. ${unfolded.snd.pp}";
  top.freeVars = remove(id, body.freeVars);
}

abstract production app
top::Term ::= t1::Term t2::Term
{
  top.pp =
    ppConcat([
      case t1 of
      | var(_) -> t1.pp
      | app(_, _) -> t1.pp
      | _ -> parens(t1.pp)
      end,
      space(),
      case t2 of
      | var(_) -> t2.pp
      | _ -> parens(t2.pp)
      end]);
  top.freeVars = union(t1.freeVars, t2.freeVars);
}

-- Named "letT" to avoid conflicting with Silver let keyword
abstract production letT
top::Term ::= id::String t::Term body::Term
{
  top.pp = pp"let ${text(id)} = ${t.pp} in ${body.pp}";
  top.freeVars = union(t.freeVars, remove(id, body.freeVars));
}

function unfoldAbsVars
([String], Term) ::= t::Term
{
  return
    case t of
    | abs(n, body) ->
      let rest::([String], Term) = unfoldAbsVars(body)
      in (n :: rest.fst, rest.snd)
      end
    | _ -> ([], t)
    end;
}

-- Helper function
function freshVar
String ::=
{
  return "a" ++ toString(genInt());
}

