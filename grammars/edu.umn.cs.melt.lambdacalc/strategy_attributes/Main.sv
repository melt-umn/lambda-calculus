grammar edu:umn:cs:melt:lambdacalc:strategy_attributes;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:lambdacalc:concretesyntax;
imports edu:umn:cs:melt:lambdacalc:abstractsyntax;

function main
IOVal<Integer> ::= args::[String] ioIn::IO
{
  local fileName :: String = head(args);
  local result::IOMonad<Integer> = do {
    if length(args) != 1 then do {
      printM("Usage: java -jar strategy_attributes.jar [file name]\n");
      return 1;
    } else do {
      isF::Boolean <- isFileM(fileName);
      if !isF then do {
        printM("File \"" ++ fileName ++ "\" not found.\n");
        return 2;
      } else do {
        text :: String <- readFileM(fileName);
        let result :: ParseResult<Term_c> = parse(text, fileName);
        if !result.parseSuccess then do {
          printM(result.parseErrors ++ "\n");
          return 3;
        } else do {
          let ast::Term = result.parseTree.ast;
          printM(show(80, ast.pp) ++ "\n\n");
          printM(show(80, evaluate(ast).pp) ++ "\n");
          return 0;
        };
      };
    };
  };
  
  return evalIO(result, ioIn);
}
