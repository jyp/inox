module Inox where

import qualified Data.Map.Strict as Map
import qualified Control.Monad.State as MS

data PositiveType
    = PositiveType :*: PositiveType
    | One
    | Shift NegativeType

newtype NegativeType = Dual PositiveType

newtype Variable = Variable Integer -- ?? We could use strings for ease of read.
  deriving (Eq,Ord)

data Value -- positive terms
    = Pair Value Value
    | Unit
    | LetForce (Map.Map Variable ()) Variable Command
    | Id Variable

data Computation -- negative terms
   = LetPair Variable Variable Command
   | LetUnit Command
   | ForceWith Value
   | CC Variable Command


data Command = Command Value Computation

subst :: Variable -> Value -> Command -> Command
subst _x _v _c = error "subst: TODO"

reduce :: Command -> Command
reduce (Command Unit (LetUnit c)) = c
reduce (Command (Pair a b) (LetPair x y c)) = subst x a $ subst y b $ c
reduce (Command (LetForce _gamma x c) (ForceWith a)) = subst x a c
reduce (Command a (CC x c)) = subst x a c
reduce _ = error "reduce: ill-typed"

data State
  = Run Environment Closure Computation

newtype Address = Address Integer
  deriving (Eq,Ord)

data Closure -- ^ value
  = CPair Closure Closure
  | CUnit
  | ClosedComputation Environment Variable Command -- ^ closure

type Environment = Map.Map Variable Closure

-- | Helper to perform closing
run' :: Environment -> Command -> State
run' e (Command v c) = Run e' clo c
  where (clo,e') = MS.runState (close v) e

-- | Abstract Machine
run :: State -> State
run (Run e CUnit (LetUnit c)) = run' e c
run (Run e (CPair a b) (LetPair x y c)) = run' (Map.insert x a $ Map.insert y b e) c
run (Run e (ClosedComputation e' x c) (ForceWith u)) =
  run' (Map.insert x clo e') c
  -- TODO: check `_mt` is empty?
  where (clo,_mt) = MS.runState (close u) e
run (Run e v (CC x c)) =
  run' (Map.insert x v e) c
run _ = error "run: ill-typed"

close :: Value -> MS.State Environment Closure
close Unit = return CUnit
close (Pair a b) = CPair <$> close a <*> close b
close (Id x) = do
  e <- MS.get
  MS.put $ Map.delete x e
  let (Just v) = Map.lookup x e
  return v
close (LetForce gamma x c) = do
  e <- MS.get
  let e' = Map.intersectionWith (\a _ -> a) e gamma
  MS.put $ Map.difference e gamma
  return $ ClosedComputation e' x c
