{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UnicodeSyntax #-}

module FocPol where

import Data.Monoid hiding (All)
----------------------------------------------
-- Types

{-
    Γ+, P |-
------------------- Up
    Γ+, ↑P |-

    Γ, N |-
--------------- Down
    Γ, ↓N |-
-}

data Type where
  Perp :: Type -> Type -- interpreted as shift in the polarised logic.
  (:*), (:+)  :: Type -> Type -> Type
  I, O :: Type
  Ex :: (Type -> Type) -> Type
  Var :: String -> Type
 -- deriving (Show)

instance Show Type where
  show t0 = case t0 of
    (t :* u) -> show t <> "*" <> show u
    (t :+ u) -> show t <> "+" <> show u
    (t :| u) -> show t <> "|" <> show u
    (t :& u) -> show t <> "&" <> show u
    I -> "1"
    O -> "0"
    Var x -> x
    Perp x -> "~" <> show x

dual :: Type -> Type
dual (Perp x) = x
dual x = Perp x

pattern x :| y <- Perp ((dual -> x) :* (dual -> y))
pattern x :& y <- Perp ((dual -> x) :+ (dual -> y))
pattern T = Perp O
pattern B = Perp I
pattern All t <- Perp (Ex ((dual .) -> t)) -- ?FIXME? Dualise the arg?

par :: Type -> Type -> Type
par x y = Perp (dual x :* dual y)

------------------------------------------------
-- Terms

data LL r n where
  Tensor :: r -> n -> n -> LL r n -> LL r n
  Par :: r -> n -> LL r n -> n -> LL r n -> LL r n
  Plus :: r -> n -> LL r n -> n -> LL r n -> LL r n
  With :: Bool -> r -> n -> LL r n -> LL r n
  One :: r -> LL r n -> LL r n
  Zero :: r -> LL r n
  Bot :: r -> LL r n
  Exist :: r -> String -> n -> LL r n -> LL r n
  Forall :: r -> Type -> n -> LL r n -> LL r n
  Ax :: r -> r -> LL r n
  Cut :: Type -> n -> LL r n -> n -> LL r n -> LL r n

  Down :: r -> n -> LL r n -> LL r n
  Up   :: r -> n -> LL r n -> LL r n
 deriving (Show)
------------------------------------------------
-- Values

-- Positive values (values inhabiting positive types).
data Pos r where
  VExist :: Type -> Val r -> Pos r
  VTensor :: Val r -> Val r -> Pos r
  VPlus :: Bool -> Val r -> Pos r
  VOne  :: Pos r
  VAtom :: String -> Pos r
  -- for type variables and builtin atoms.
 deriving Show

instance Show (a -> b) where
  show _ = "<FUN>"

-- Negative values (values inhabiting positive types)
type Neg r = Pos r -> r
type NegNeg r = Neg r -> r

-- Anything
data Val r where
  Pos :: Pos r -> Val r
  Neg :: Neg r -> Val r
  Shift :: NegNeg r -> Val r
 deriving Show

-------------------------------------
-- Evaluator.

-- | Map names (n) to values and their types.
type Env n r = [(n,(Val r,Type))]

-- | Evaluate a variable to a positive (double neg) value (variable has a negative type in the env)
evalP :: Eq n => Env n r -> n -> Type -> LL n n -> NegNeg r
evalP env name ty t x = coeval ((name,(Neg x,ty)):env) t

-- | Evaluate a variable to a negative value (variable has a positive type in the env)
-- evalN :: Eq n => Env n r -> n -> Type -> LL n n -> Neg r
evalN :: Eq n => Env n r -> n -> Type -> LL n n -> Pos r -> r
evalN env name ty t = (\x -> coeval ((name,(Pos x,ty)):env) t)

-- Note: both of the above extractions of a 'value' can be done by pushing the
-- dual in the environment and proceed with co-evaluation.

-- Evaluate a variable in the environment.
eval :: Eq n => Env n r -> n -> Type -> LL n n -> (Val r -> r) -> r
-- Attention: if the type of the variable is neg, then the value is pos and vice versa
-- eval env name ty@(Perp _) t k = k $ Shift $ evalP env name ty t -- Non-focusing version (No-Foc)
eval env name ty@(Perp _) t n = evalP env name ty t $ \q -> n (Pos q) -- ! Don't create shift here !
eval env name ty t k = k $ Neg $ evalN env name ty t

-- | View a positive value as a double negative one. (shift)
asShift :: Val r -> (Pos r -> r) -> r
asShift (Shift n) = n
asShift (Pos x) = \k -> k x -- One can get rid of shifts as long as we promise
                            -- to return a compatible effect (r).

-- We define three patterns for values: positive, negative and shift. To get
-- full match we need only S and N. P is optional as it can be converted to S
-- using 'asShift'.
pattern S k <- (asShift -> k)
pattern P n = Pos n
pattern N n = Neg n

-- | Make all the variables in the environment interact and finally return an
-- effect (r).
coeval :: Eq n => Env n r -> LL n n -> r
coeval env t = case t of
  Zero _ -> error "input program not well typed"
  Cut ty x t' y u' -> eval env x (dual ty) t' $ \a -> -- evaluate one side
                      coeval ((y,(a,ty)):env) u'      -- get the result and co-eval the rest.
  Ax x y -> case (lookup x env, lookup y env) of
     (Just (N k,_), Just (S p,_)) -> p k
     (Just (S p,_), Just (N k,_)) -> p k
  Bot z -> case lookup z env of
    Just (N k,I) -> k VOne
  One z t' -> case lookup z env of
    Just (S k,Perp I) -> k $ \VOne -> coeval env t'
  Tensor z x y t' -> case lookup z env of
    Just (S k,ta :* tb) -> k $ \(VTensor a b) -> coeval ((x,(a,ta)):(y,(b,tb)):env) t'
  Par z x t' y u' ->  case lookup z env of
    Just (N k,ta :| tb) -> eval env x ta t' $ \a ->
                           eval env y tb u' $ \b -> k $ VTensor a b
  Plus z x t' y u' -> case lookup z env of
    Just ((S k), ta :+ tb) -> k $ \(VPlus choice a) -> if choice
                                                   then coeval ((x,(a,ta)):env) t'
                                                   else coeval ((y,(a,tb)):env) u'
  With c z x t' -> case lookup z env of
    Just (N k, ta :& tb) -> eval env x (if c then ta else tb) t' $ \a -> k $ VPlus c a
  Exist z _tvar x t' -> case lookup z env of
    Just (S k, Ex tt) -> k $ \(VExist ty a) -> coeval ((x,(a,tt ty)):env) t'
  Forall z ty x t' -> case lookup z env of
    Just (N k, All tt) -> eval env x (tt ty) t' $ \a -> k $ VExist ty a -- FIXME Type ???

  -- where pattern Look x <- (flip lookup env -> Just x)
 -- hahahah: Pattern synonym declarations are only valid in the top-level scope

----------------------------------
-- Reifier

-- This is the reification part of NbE (as explained to me by Martin Löf): it
-- turns an abstract variable (n) of a given type into a value standing for n.

-- toVal :: (n ~ String, r ~ LL n n) => n -> Type -> Val r
-- | Top-level conversion. Pattern-match on the type and reify as appropriate.
-- toVal :: forall r n. Reifier n r => n -> Type -> Val r
toVal x (Perp t) = Neg $ \a -> Down (x,Perp t) (x_arg,Perp t) $ coreify x_arg (Perp t) (Pos a)
  where x_arg = fresh x "arg"
-- quirk:if we don't have this then the negative atoms coming from the
-- environment will not be considered as closures, but as variables we can just
-- write into.
toVal x (Perp t) = Neg $ \a -> coreify x (Perp t) (Pos a)
toVal x t = Shift $ \k -> reify x t $ \(P a) -> k a
-- The above line is the only place in the where shift is created. (Shifts
-- created in 'asShift' are matched in 'coeval', and thus removed immediately.)


fresh :: String -> String -> String
fresh nm suff = nm ++ "_" ++ suff

-- reify :: (n ~ String, r ~ LL n n) => n -> Type -> (Val r -> r) -> r
reify x t0 k = case t0 of
  t :* u -> Tensor (x,t0) (nx,t) (ny,u) $ reify nx t $ \a -> reify ny u $ \b -> kp (VTensor a b)
  t :+ u -> Plus (x,t0) (nx,t) (reify nx t (kp . VPlus True)) (ny,u) (reify ny u (kp . VPlus False))
  Ex t -> Exist (x,t0) nt (nx,tt) $ reify nx (tt) (kp . VExist (Var nt))
    where tt = t (Var nt)
  I -> One (x,I) $ kp VOne
  O -> Zero (x,O)
  Var _ -> kp (VAtom x)
  neg@(Perp _) -> k $ Neg $ \v -> Down (x,t0) (nx,t0) $ coreify nx neg (Pos v)
 where kp = k . Pos
       nx = fresh x "x"; ny = fresh x "y"; nt = fresh x "t"

-- One can see that the reified value is focused, because:
-- 1. As long as one finds negative types, one remains in "coreify"
-- 2. The code (effect) built along this chain of calls is not interspersed with other code
-- 3. Coreify is never passed a Shift. This is because Shifts are only created in "toVal",
-- and "toVal" does not feed its shift to reify/coreify.
-- coreify :: (n ~ String, r ~ LL n n) => n -> Type -> Val r -> r
-- coreify x typ@(Perp _) (S k) = k $ \v -> case (typ,v) of -- (No-Foc)
coreify x typ@(Perp _) (P v) = case (typ,v) of
    (t :| u,VTensor a b) -> Par (x,typ) (nx,t) (coreify nx t a) (ny,u) (coreify ny u b)
    -- (t :& u,VPlus c a) -> With c x nx (coreify nx (if c then t else u) a)
    -- (All t,VExist ty a) -> Forall x ty nx (coreify nx (t ty) a)
    (B,VOne) -> Bot (x,B)
    (Perp (Var _),VAtom y) -> Ax (x,typ) (y,dual typ)
  where nx = fresh x "x"; ny = fresh x "y"
coreify x typ (N k) = Up (x,typ) (nx,typ) $ reify nx typ $ \(P a) -> k a -- Pattern ok because typ is positive
  where nx = fresh x "x"


-- | Compile a focused, polarised logic into C.
compileC ∷ LL (String, Type) (String, Type) → String
compileC t0 = case t0 of
  Tensor (z,_) (x,t) (y,u) t' ->
    cDecl' t x <> " = " <> z <> ".fst;\n" <>
    cDecl' u y <> " = " <> z <> ".snd;\n" <>
    compileC t'
  One _ t' -> "nop();\n" <> compileC t'
  Zero (x,_) -> "abort(" <> show (x <> " cannot happen") <> ");\n"
  Ax (x,_) (y,t) -> cDecl' t x <> "=" <> y <> ";\n"
  Down (z,_) (x,_) t' ->
    compileC t' <>
    "CALL" <> parens (z <> ", " <> x) <> ";\n"

  -- compiling negatives, by construction of the eliminated variable.
  Par (z,t) (x,_) t' (y,_) u' -> compileC t' <>
                     compileC u' <>
                     cDecl' (dual t) z <> " = " <> braces (".left = " <> x <> ";\n.right = " <> y) <> ";\n"
  Bot (z,_) -> cDecl' I z <> " = {};\n"
  Up (z,_) (x,t) t' ->
     "void " <> xfun <> "(ENV," <> cDecl' t x <> ") {\n" <> compileC t' <> "}\n" <>
     cDecl' (dual t) z <> " = MK_CLOSURE(ENV,&" <> xfun <> ");\n"
   where xfun = fresh x "fun"

parens x = "(" <> x <> ")"
braces x = "{" <> x <> "}"
pair x y = parens $ x <> "," <> y


cDecl :: Type -> Maybe String -> String
cDecl t0 n = case t0 of
    (t :* u) -> "struct " <> braces (cDecl' t "fst" <> ";\n" <> cDecl' u "snd" <> ";\n") <> nn
    I -> "struct {} " <> nn
    (Var x) -> x <> " " <> nn
    (Perp x) -> "void " <> parens ("*" <> nn)
  where nn = case n of Just x -> x; Nothing -> ""

-- cFun "void " <> parens("*" <> nn) <> parens (cDecl x Nothing)

cDecl' ∷ Type → String → String
cDecl' t n = cDecl t (Just n)

freeVars :: Val r -> [String]
freeVars (Neg _) = []
freeVars (Pos p) = case p of
  VAtom x -> [x]
  VExist _ v -> freeVars v
  VTensor a b -> freeVars a <> freeVars b
  VPlus _ a -> freeVars a
  VOne -> []

-- normalize :: forall r n. (Reifier n r, Eq n) => [(n, Type)] -> LL n n -> r
normalize ctx = coeval [(n, (toVal n t,t)) | (n,t) <- ctx]


compile (ctx,input) = compileC $ (normalize ctx input)

------
-- ex
trivial, foc, simpl :: n ~ String => ([(n,Type)],LL n n)
trivial = ([("x",Var "A"),("y",Perp (Var "A"))], Ax "x" "y")

simpl = ([("xy",Perp (Var "A") `par` Var "B")
         ,("x'",Var "A")
         ,("y'",Perp (Var "B"))]
         ,Par "xy" "x" (Ax "x" "x'") "y" (Ax "y" "y'"))

foc = ([("aPbPc",Var "a" `par` (Var "b" `par` Var "c"))
       ,("a'",Perp (Var "a"))
       ,("x'",Perp (Var "x"))
       ,("xPb'Tc'",(Var "x") `par` (Perp (Var "b") :* Perp (Var "c")))],
       Par "aPbPc"
       "a" (Ax "a" "a'")
       "bPc" (Par "xPb'Tc'"
              "x" (Ax "x" "x'")
              "b'Tc'" (Tensor "b'Tc'" "b'" "c'"
                       (Par "bPc"
                        "b" (Ax "b" "b'")
                        "c" (Ax "c" "c'")))))
