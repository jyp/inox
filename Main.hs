

import Text.PrettyPrint.Compact
import Inox
import ParseCore

main :: IO ()
main =
  case parse "< () | let () = . in Done >" :: Either String Command of
    Right c -> putStrLn $ render $ pretty c
    Left e -> putStrLn $ "Parsing error: " ++ e
