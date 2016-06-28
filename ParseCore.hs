{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleContexts,
  FunctionalDependencies #-}

-- Boiler plate to convert types generated with bnfc to Inox datatypes.

module ParseCore where

import Data.Either ()
import qualified Data.Map.Strict as Map
import qualified Bnf.Core.Abs as Abs
import Bnf.Core.Lex
import Bnf.Core.Par
import Bnf.Core.ErrM (Err(..))
import Inox

class Abs a c | a -> c where
  conv :: a -> c

class (Abs abs a) => Parse abs a | a -> abs where
  parse :: String -> Either String a
  parse = fmap conv . wrapErr . parser . tokens

  parser :: [Token] -> Err abs


instance Parse Abs.Value Value where
  parser = pValue

instance Parse Abs.Computation Computation where
  parser = pComputation

instance Parse Abs.Command Command where
  parser = pCommand

wrapErr :: Err a -> Either String a
wrapErr (Ok a) = Right a
wrapErr (Bad s) = Left s

instance Abs Abs.Variable Variable where
  conv (Abs.Var (Abs.Ident x)) = Variable x


instance Abs Abs.PositiveType PositiveType where
  conv (Abs.Tensor t1 t2) = conv t1 :*: conv t2
  conv Abs.One = One
  conv (Abs.Shift n) = Shift (conv n)


instance Abs Abs.NegativeType NegativeType where
  conv (Abs.Dual t) = Dual (conv t)


instance Abs Abs.Value Value where
  conv (Abs.Pair u v) = Pair (conv u) (conv v)
  conv Abs.Unit = Unit
  conv (Abs.LetForce gamma x t c) =
    let gamma' = Map.fromList $ map (\y -> (y,())) (map conv gamma) in
      LetForce (conv t) gamma' (conv x) (conv c)
  conv (Abs.Id x) = Id (conv x)

instance Abs Abs.Computation Computation where
  conv (Abs.LetPair x y c) =
    LetPair (conv x) (conv y) (conv c)
  conv (Abs.LetUnit c) = LetUnit (conv c)
  conv (Abs.ForceWith v) = ForceWith (conv v)
  conv (Abs.CC x c) = CC (conv x) (conv c)


instance Abs Abs.Command Command where
  conv (Abs.Com v n) = Command (conv v) (conv n)
  conv Abs.Done = Done
