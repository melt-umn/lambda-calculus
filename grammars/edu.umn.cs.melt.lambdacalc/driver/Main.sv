grammar edu:umn:cs:melt:lambdacalc:driver;

imports core:monad;
imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:lambdacalc:concretesyntax;
imports edu:umn:cs:melt:lambdacalc:abstractsyntax;

parser parse::Term_c {
  edu:umn:cs:melt:lambdacalc:concretesyntax;
}

function main
IOVal<Integer> ::= args::[String] ioIn::IO
{
  local fileName :: String = head(args);
  local result::IOMonad<Integer> = do (bindIO, returnIO) {
    if length(args) != 1 then {
      printM("Usage: java -jar lambdacalc.jar [file name]\n");
      return 1;
    } else {
      isF::Boolean <- isFileM(fileName);
      if !isF then {
        printM("File \"" ++ fileName ++ "\" not found.\n");
        return 2;
      } else {
        text :: String <- readFileM(fileName);
        result :: ParseResult<Term_c> = parse(text, fileName);
        if !result.parseSuccess then {
          printM(result.parseErrors ++ "\n");
          return 3;
        } else {
          ast::Term = result.parseTree.ast;
          printM(show(80, ast.pp) ++ "\n\n");
          printM(show(80, norm(ast).pp) ++ "\n");
          return 0;
        }
      }
    }
  };
  
  return evalIO(result, ioIn);
}
