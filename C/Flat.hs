{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}

module C.Flat where

import CLL
import Data.Monoid
import Data.List
import Data.Function
import C.Common

-- Could be used to 'optimise' structures.
-- data Atom = AVar String
--           | Closure

-- flatten :: Type -> [Atom]
-- flatten (t :* u) = flatten t ++ flatten u
-- flatten (Perp _) = [Closure]
-- flatten (Var t) = [AVar t]


sizeOf :: Type -> C -> C
sizeOf (Var t) _ = "sizeof(" <> lit t <> ")"
sizeOf (t :* u) arr = sizeOf t arr ~+~ sizeOf u (arr ~+~ sizeOf t arr)
sizeOf (Perp _) arr = "CLOSURE_SIZE(" <> arr <> ")"

decl x = "char* " <> var x

sizeOfVar ∷ (String, Type) → C
sizeOfVar x@(_,t) = sizeOf t (var x)

compileC ∷ LL (String, Type) (String, Type) → C
compileC t0 = case t0 of
  Tensor z x y t' ->
    stmt (decl x <> " = " <> var z) <>
    stmt (decl y <> " = " <> var z ~+~ sizeOfVar x) <>
    compileC t'
  One _ t' -> "NOP();\n" <> compileC t'
  Zero x -> "ABORT(" <> var x <> ");\n"
  Ax x y -> stmt (decl x ~=~ var y)

  Down z x t' ->
    stmt ("char " <> var x <> "[" <> compileSize t' <> "]") <>
    cocompileC t' <>
    stmt (cCall "CALL" [var z,var x,sizeOfVar x])


compileSize :: LL (String, Type) (String, Type) → C
compileSize t0 = case t0 of
  Ax x y -> sizeOfVar y
  Par z x t' y u' -> compileSize t' ~+~ compileSize u'
  Bot z -> "0"
  Up z x@(xn,t) t' -> cCall "ENV_TO_CLOSURE_SIZE" (fmap sizeOfVar env')
    where (Code _ env _ _ _) = compileC t'
          env' = nubBy ((==) `on` fst) (env \\\ [xn])


cocompileC :: LL (String, Type) (String, Type) → C
cocompileC t0 = case t0 of
  Ax x y -> stmt $ cCall "memcpy" [var x, var y, sizeOfVar y]
  Par z x t' y u' -> stmt (decl x ~=~ var z) <>
                     stmt (cocompileC t') <>
                     stmt (decl x ~=~ var z ~+~ compileSize t') <>
                     stmt (cocompileC u')

  Bot z -> mempty
  Up z@(zn,_) x@(xn,_) t' ->
     def ("void " <> zfun <> parens (commas ["int param__SIZE",
                                        "char " <> var x <> "[param_SIZE]",
                                        "int env__SIZE",
                                        "char env[env_SIZE]"]) <>
          braces (
             mconcat [stmt (decl v <> "= env" <> var v) <>
                      stmt ("env += " <> sizeOfVar v)
                     | v <- env'] <> -- TODO: unpack env
             t'c)) <> -- FIXME: hoist to the top level.
     stmt (cCall "CLOSURE_FUNC"     [var z] ~=~ zfun) <>
     stmt (cCall "CLOSURE_ENV_SIZE" [var z] ~=~ cSum (fmap sizeOfVar env')) <>
     stmt (decl z <> "_env = " <> (cCall "CLOSURE_ENV" [var z])) <>
     mconcat [stmt (cCall "memcpy" [zenv,var v,sizeOfVar v]) <>
              stmt (zenv <> " += " <> sizeOfVar v)| v <- env']
    where zenv = lit $ fresh zn "env"
          zfun = lit $ quoteVar $ fresh zn "fun"
          t'c@(Code _ env _ _ _) = compileC t'
          env' = nubBy ((==) `on` fst) (env \\\ [xn])

main ∷ IO ()
main = writeFile "simp.c" $ compile simpl
