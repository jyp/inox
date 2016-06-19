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

module C.Common where

import Data.String
import Data.Monoid
import CLL

(~+~) :: C -> C -> C
x ~+~ y = x <> "+" <> y

cSum ∷ [C] → C
cSum [] = "0"
cSum xs = foldr1 (~+~) xs

(~=~) :: C -> C -> C
x ~=~ y = x <> "+" <> y

(<+>) ∷ ∀ m. (IsString m, Monoid m) ⇒ m → m → m
x <+> y = x <> " " <> y


commas [] = ""
commas xs = foldr1 (\x y -> x <> ", " <> y) xs
parens x = "(" <> x <> ")"
braces x = "{\n" <> x <> "}"
pair x y = parens $ x <> "," <> y

data C = Code {cCode :: String, cOccs :: [(String,Type)], cDecls :: [String], cDefs :: [String], cStructs ::  [(String,C)]}

instance IsString C where
  fromString = lit

lit ∷ String → C
lit s = Code s [] [] [] []

var ∷ (String,Type) → C
var (s,t) = Code (quoteVar s) [(s,t)] [] [] []

dcl :: String -> C
dcl s = Code (quoteVar s) [] [s] [] []

def :: C -> C
def (Code s occs decls defs structs) = Code [] occs decls (s:defs) structs

cCast ∷ C -> C -> C
cCast typ expr = parens ("*" <> parens (typ <> "*") <> parens ("&" <> expr))


cStructDef :: String -> C -> C
cStructDef name body = Code ("struct " <> n) [] [] [] [(n,stmt ("struct " <> lit n <> braces body))]
  where n = quoteVar name


instance Monoid C where
  mempty = Code mempty mempty mempty mempty mempty
  mappend (Code c1 v1 d1 f1 s1) (Code c2 v2 d2 f2 s2) = Code (c1 <> c2) (v1 <> (v2 \\\ d1)) (d1 <> d2) (f1 <> f2) (s1 <> s2)

quoteVar :: String -> String
quoteVar = concatMap quoteChar

quoteChar :: Char -> String
quoteChar '_' = "__"
quoteChar '\'' = "_p"
quoteChar x | isAlphaNum x = [x]
            | otherwise = show (ord x)

stmt ∷ C → C
stmt x = x <> lit ";\n"

-- would be nice to use a map for this to avoid nubBy complexity. However we
-- need to remember the order things appeared so that we can sort the
-- declarations in reverse dependency order.
cleanStructs = map snd . nubBy ((==) `on` fst) . reverse


compile ∷ ([(String, Type)], LL String String) → String
compile (ctx,input) = cCode $
  "#include <cf.h>\n" <>
  mconcat (cleanStructs (cStructs cctx <> cStructs t'c)) <>
  lit (mconcat (cDefs t'c)) <>
  ("void main_function(" <> cctx <> ") " <> braces t'c)
  where           t'c = compileC t'
                  t' = (normalize ctx input)
                  cctx = commas [cDecl' x | x <- ctx]
