

import Text.PrettyPrint.Compact
import Inox

main :: IO ()
main = putStrLn $ render $ pretty $ Command Unit (LetUnit Done)
