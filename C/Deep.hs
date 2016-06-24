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

module C.Deep where

import CLL
import Data.Monoid
import Data.List
import Data.Function
import C.Common


cDecl (n,t) = cDecl' t (Just n)
coDecl (n,t) = cDecl' (dual t) (Just n)

cStruct :: [(String,Type)] -> C
cStruct fields = (mconcat [cDecl (f,t) <> ";\n" | (f,t) <- fields])

cTypeName :: Type -> String
cTypeName (t :* u) = "p" <> cTypeName t <> "_" <> cTypeName u
cTypeName (I) = "i"
cTypeName (Var x) = "v" <> x
cTypeName (Perp t) = "n" <> cTypeName t

cName ∷ Maybe String → C
cName (Just x) = dcl x
cName Nothing = ""

cFun :: String -> C -> Type -> Maybe String -> C
cFun n env t arg = "void " <> lit n <> "(" <> cDecl' t arg <> "," <> env <> ")"

cDecl' :: Type -> Maybe String -> C
cDecl' t0 n = case t0 of
    (t :* u) -> cStructDef (cTypeName t0) (cStruct [("fst",t),("snd",u)]) <+> cName n
    I -> cStructDef (cTypeName t0) (cStruct []) <+> cName n
    (Var x) -> lit x <> " " <> cName n
    (Perp t) -> cStructDef (cTypeName t0)
                  (cFun "(*code)" "char*" t Nothing <> ";\n" <>
                   "char env[0];") <> "*" <+> cName n


-- | Compile a focused, polarised logic into C.
compileC ∷ LL (String, Type) (String, Type) → C
compileC t0 = case t0 of
  Tensor z x y t' ->
    cDecl x <> " = " <> var z <> ".fst;\n" <>
    cDecl y <> " = " <> var z <> ".snd;\n" <>
    compileC t'
  One _ t' -> "NOP();\n" <> compileC t'
  Zero x -> "ABORT(" <> var x <> ");\n"
  Ax x y -> stmt (coDecl x <> "=" <> var y)

  Down z (x,_) t' ->
    cocompileC t' <>
    var z <> "->code" <> parens (commas [lit (quoteVar x),var z <> "->env"]) <> ";\n"


  Bang z x t' ->
    stmt (cCall "BOX_DEREF" [var z]) <>
    stmt (cDecl x <> " = " <> cCall "BOX_CONTENTS" [var z]) <>
    compileC t'

  Contract z x y t' ->
    stmt (cDecl x <> " = " <> var z) <>
    stmt (cDecl y <> " = " <> var z) <>
    stmt (cCall "BOX_REF_COUNT" [var z] <> "++") <>
    compileC t'

  Derelict z t' ->
    stmt (cCall "BOX_DEREF" [var z]) <>
    compileC t'

-- | Compiling negatives, by construction of the eliminated variable.
cocompileC :: LL (String, Type) (String, Type) → C
cocompileC t0 = case t0 of
  Ax x y -> stmt (coDecl x <> "=" <> var y)
  Par z x t' y u' ->
    cocompileC t' <>
    cocompileC u' <>
    coDecl z <> " = " <> braces (".fst = " <> var x <> ",\n.snd = " <> var y) <> ";\n"
  Bot z -> stmt (cDecl z <> " = {}")
  Up z x@(xn,t) t' ->
     def (cFun xfun (envStruct <> "* env") t (Just xn) <>
          braces (mconcat [stmt (cDecl v <> "= env->" <> var v) | v <- env'] <>
                  -- cCall "free(CLOSURE_OF(env))"
                  t'c )) <> -- FIXME: hoist to the top level.
     stmt (coDecl z <> " = " <> cCall "malloc" ["4 /* fixme */+" <>  cCall "sizeof" [envStruct]]) <>
     stmt (envStruct <> " *" <> cXenv <> " = " <> var z <> "-> env") <>
     mconcat [stmt $ cXenv <> "->" <> v <> " = " <> v | v <- map var env'] <>
     stmt (var z <> "->code = " <> lit xfun) -- fixme: add a cast
     -- stmt (cCall "memcpy" [var z <> "->env ","&" <> cXenv,cCall "sizeof" [cXenv]])
    where xenv = (xn ++ "_env")
          xfun = quoteVar $ fresh xn "fun"
          t'c@(Code _ env _ _ _) = compileC t'
          env' = nubBy ((==) `on` fst) (env \\\ [xn])
          envStruct = cStructDef (cEnvName env') (cStruct env')
          cXenv = lit (quoteVar xenv)

cEnvName :: [(String,Type)] -> String
cEnvName env = "e" <> mconcat ["f_" <> f <> "_" <> cTypeName t | (f,t) <- env]


compile ∷ ([(String, Type)], LL String String) → String
compile (ctx,input) = cCode $
  "#include \"cd.h\"\n" <>
  mconcat (cleanStructs (cStructs cctx <> cStructs t'c)) <>
  lit (mconcat (cDefs t'c)) <>
  ("void main_function(" <> cctx <> ") " <> braces t'c)
  where           t'c = compileC t'
                  t' = (normalize ctx input)
                  cctx = commas [cDecl x | x <- ctx]

main ∷ IO ()
main = writeFile "simp.c" $ compile simpl
