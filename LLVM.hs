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

module LLVM where

import CLL
import Data.Monoid
import Data.List
import Data.Function
import C.Common hiding (stmt,dcl')


stmt x = x <> "\n"

struct :: [Type] -> C
struct fields = braces $ commas $ map vmtype fields

typeName :: Type -> String
typeName (t :* u) = "p" <> typeName t <> "_" <> typeName u
typeName (I) = "i"
typeName (Var x) = "v" <> x
typeName (Perp t) = "n" <> typeName t


cFun :: String -> Type -> String -> C -> C
cFun n t arg env = "void " <> lit n <> "(" <> vmtype t <> " " <> lit arg <> "," <> env <> ")"

percent x = "%" <> x

vmtype :: Type -> C
vmtype t0 = case t0 of
    (t :* u) -> struct [t,u]
    I -> struct []
    (Var x) -> percent (lit x)
    (Perp t) -> cloType t <> " *"

funType t = cFun "" t "" "i8 *" <> " *"
cloType t = braces (commas [funType t, "[0 x i8]"])

dcl' :: (String, Type) -> C
dcl' = percent . dcl . fst
parameter (s,t) =  vmtype t <> " " <> dcl' (s,t)
var' (s,t) = vmtype t <> " " <> percent  (var (s,t))
lit' = percent . lit

stmts = mconcat . map stmt
-- | Compile a focused, polarised logic into C.
compileC ∷ LL (String, Type) (String, Type) → C
compileC t0 = case t0 of
  Tensor z x y t' ->
    stmts [dcl' x <> " = extractvalue " <> var' z <> ", 0\n"
          ,dcl' y <> " = extractvalue " <> var' z <> ", 1\n"] <>
    compileC t'
  One _ t' -> "\n" <> compileC t'
  Zero x -> "call ABORT(" <> var x <> ")\n"
  Ax x y -> stmt (dcl' x <> "= add " <> var' y <> ", 0")

  Down z (x,t@(Perp u)) t' ->
    cocompileC t' <>
    stmts
    [ tmp z "code_ptr" ~=~ "getelementptr " <> cloType u <> ", " <> var' z <> ", i32 0, i32 0"
    , tmp z "code" ~=~ "load " <> funType u <> ", " <> funType u <> "* " <> tmp z "code_ptr"
    , tmp z "env " ~=~ "getelementptr " <> cloType u <> ", " <> var' z <> ", i32 0, i32 1, i32 0"
    , "musttail call void " <> tmp z "code" <> parens
      (commas [vmtype u <+> "%" <> lit (quoteVar x), "i8* " <> tmp z "env"])
    , "ret void" ]

typOf = vmtype . snd
num = lit . show

tmp ∷ ∀ t. (String, t) → String → C
tmp (s,_) suff = "%" <> lit (quoteVar s) <> "_" <> lit suff

-- | Compiling negatives, by construction of the eliminated variable.
cocompileC :: LL (String, Type) (String, Type) → C
cocompileC t0 = case t0 of
  Ax x y -> stmt (dcl' x <> "= add " <> var' y <> ", 0")
  Par z x t' y u' ->
    cocompileC t' <>
    cocompileC u' <>
    tmp z "zero" <> " = insertvalue " <> typOf z <> " undef, " <> var x <> ", 0\n" <>
    dcl' z <> " = insertvalue " <> typOf z <> " " <> tmp z "zero" <> ", "  <> var y  <> ",1\n"
  Bot z -> "; BOT \n"
  Up z x@(xn,t) t' ->
     def ("define " <> cFun xfun t xnparam (envStruct <> "* %env")<>
          braces (stmt mempty <>
                  mconcat [stmt (tmp v "ptr" <> " = getelementptr " <> envStruct <> ", " <>
                                                    envStruct <>  "* %env, i32 0, i32 " <> num i) <>
                           stmt (dcl' v <> "= load " <> typOf v <> ", " <> typOf v <> "* " <> tmp v "ptr")
                          | (v,i) <- zip env' [0..]] <>
                  -- cCall "free(CLOSURE_OF(env))"
                  t'c )) <>
     stmt (dcl' z <> " = call i8 * " <> cCall "@malloc" ["4 /* fixme */+" <>  cCall "sizeof" [envStruct]]) <>
     mconcat [stmt (tmp v "ptr" <> " = getelementptr " <> envStruct <> ", " <> envStruct <> "* " <> tmp z "" <> ", i32 0, i32 1, i32 " <> num i) <>
              stmt ("store " <> typOf v <> tmp v "ptr" <> ", " <> var v)
             | (v,i) <- zip env' [0..]] <>
     stmt (var z <> " = getelementptr " <> typOf z <> lit xfun <> ", i32 0")
    where xfun = "@" ++ (quoteVar $ fresh xn "fun")
          t'c@(Code _ env _ _ _) = compileC t'
          env' = nubBy ((==) `on` fst) (env \\\ [xn])
          envStruct = struct $ map snd env'
          xnparam = "%" ++ quoteVar xn

cEnvName :: [(String,Type)] -> String
cEnvName env = "e" <> mconcat ["f_" <> f <> "_" <> typeName t | (f,t) <- env]


compile ∷ ([(String, Type)], LL String String) → String
compile (ctx,input) = cCode $
  -- mconcat (cleanStructs (cStructs cctx <> cStructs t'c)) <>
  stmt ("%A = type i32") <>
  stmt ("%B = type i32") <>
  lit (mconcat (fmap (<> "\n\n") (cDefs t'c))) <>
  ("define void @main_function(" <> cctx <> ") " <> braces t'c)
  where           t'c = compileC t'
                  t' = (normalize ctx input)
                  cctx = commas [parameter x | x <- ctx]

main ∷ IO ()
main = writeFile "simp.ll" $ compile simpl
