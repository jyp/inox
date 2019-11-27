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

-- | Declare a variable of the appropriate type
cDecl :: (String, Type) -> C
cDecl (n,t) = cDecl' t (Just n)

-- | Declare a variable of the dual type
coDecl :: (String, Type) -> C
coDecl (n,t) = cDecl' (dual t) (Just n)

-- | Structure fields
cStruct :: [(String,Type)] -> C
cStruct fields = mconcat [cDecl (f,t) <> ";\n" | (f,t) <- fields]

-- | Unique name for a type
cTypeName :: Type -> String
cTypeName (t :* u) = "p" <> cTypeName t <> "_" <> cTypeName u
cTypeName (t :+ u) = "s" <> cTypeName t <> "_" <> cTypeName u
cTypeName (I) = "i"
cTypeName (Var x) = "v" <> x
cTypeName (Perp t) = "n" <> cTypeName t

cName :: Maybe String → C
cName (Just x) = dcl x
cName Nothing = ""

-- Function signature
cSig :: String -> C -> Type -> Maybe String -> C
cSig n env t arg = "void " <> lit n <> "(" <> cDecl' t arg <> "," <> env <> ")"

cDecl' :: Type -> Maybe String -> C
cDecl' t0 n = case t0 of
    (t :* u) -> cStructDef (cTypeName t0) (cStruct [("fst",t),("snd",u)]) <+> cName n
    (t :+ u) -> cStructDef (cTypeName t0)
                 ("char tag;\n" <>
                  "union " <> braces
                   (cStruct [("left",t),("right",u)]) <+> "val") <+> cName n
    I -> cStructDef (cTypeName t0) (cStruct []) <+> cName n
    (Var x) -> lit x <> " " <> cName n
    (Perp t) -> cStructDef (cTypeName t0)
                  (cSig "(*code)" "char*" t Nothing <> ";\n" <>
                   "char env[0];") <> "*" <+> cName n


-- | Compile a focused, polarised logic to C.
compileC :: LL (String, Type) (String, Type) → C
compileC t0 = case t0 of
  Plus z x t y u ->
    "if (" <> var z <> "tag) {\n" <>
       stmt (cDecl x <> " = " <> var z <> ".val.left") <>
       compileC t <>
    "} else {" <>
       stmt (cDecl y <> " = " <> var z <> ".val.right") <>
       compileC u <>
    "};"
  Tensor z x y t' ->
    cDecl x <> " = " <> var z <> ".fst;\n" <>
    cDecl y <> " = " <> var z <> ".snd;\n" <>
    compileC t'
  One _ t' -> stmt "NOP()" <> compileC t'
  Zero x -> stmt ("ABORT(" <> var x <> ")")
  Ax x y -> stmt (coDecl x <> "=" <> var y)

  Down z x'@(x,_) t' ->
    stmt (coDecl x') <>
    cocompileC t' (lit (quoteVar x)) <>
    stmt (var z <> "->code" <> parens (commas [lit (quoteVar x),var z <> "->env"]))


  Bang z x t' ->
    stmt (cDecl x <> " = " <> cCall "BOX_CONTENTS" [var z]) <>
    stmt (cCall "BOX_DEREF" [var z]) <>
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
cocompileC :: LL (String, Type) (String, Type) -> C → C
cocompileC t0 target = case t0 of
  Ax _x y -> stmt (target <> "=" <> var y)
  With pol _z _x t ->
    stmt (target <> ".tag = " <> (if pol then "1" else "0")) <>
    cocompileC t (target <> ".val." <> (if pol then "left" else "right"))
  Par _z _x t' _y u' ->
    cocompileC t' (target <> ".fst") <>
    cocompileC u' (target <> ".snd")
  Bot _z -> mempty
  Up _z _x@(xn,t) t' ->
     def (cSig xfun (envStruct <> "* env") t (Just xn) <>
          braces (mconcat [stmt (cDecl v <> "= env->" <> var v) | v <- env'] <> -- load env in local vars
                  stmt (cCall "free" ["CLOSURE_OF(env)"]) <> -- free env
                  t'c )) <>
     stmt (target <> " = " <> cCall "malloc" ["4 /* fixme */+" <>  cCall "sizeof" [envStruct]]) <>
     stmt (envStruct <> " *" <> cXenv <> " = " <> target <> "-> env") <>
     mconcat [stmt $ cXenv <> "->" <> v <> " = " <> v | v <- map var env'] <> -- fill each env field
     stmt (target <> "->code = " <> lit xfun) -- fixme: add a cast
    where xenv = (xn ++ "_env")
          xfun = quoteVar $ fresh xn "fun"
          t'c@(Code _ env _ _ _) = compileC t'
          env' = nubBy ((==) `on` fst) (env \\\ [xn])
          envStruct = cStructDef (cEnvName env') (cStruct env')
          cXenv = lit (quoteVar xenv)
  Quest _ _ t' ->
    stmt (target <> " = BOX_ALLOCATE()") <>
    cocompileC t' ("*" <> target)

cEnvName :: [(String,Type)] -> String
cEnvName env = "e" <> mconcat ["f_" <> f <> "_" <> cTypeName t | (f,t) <- env]


compile :: ([(String, Type)], LL String String) → String
compile (ctx,input) = cCode $
  "#include \"cd.h\"\n" <>
  mconcat (cleanStructs (cStructs cctx <> cStructs t'c)) <>
  lit (mconcat (cDefs t'c)) <>
  ("void main_function(" <> cctx <> ") " <> braces t'c)
  where           t'c = compileC t'
                  t' = (normalize ctx input)
                  cctx = commas [cDecl x | x <- ctx]

main :: IO ()
main = writeFile "simp.c" $ compile simpl

-- >>> main
