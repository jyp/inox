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

import Data.List
import Data.String
import Data.Monoid
import CLL
import Data.Char
import Data.Function

(~+~) :: C -> C -> C
x ~+~ y = x <> " + " <> y

cSum ∷ [C] → C
cSum [] = "0"
cSum xs = foldr1 (~+~) xs

(~=~) :: C -> C -> C
x ~=~ y = x <> " = " <> y

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

dcl' :: (String,Type) -> C
dcl' = dcl . fst

dcl :: String -> C
dcl s = Code (quoteVar s) [] [s] [] []

def :: C -> C
def (Code s occs decls defs structs) = Code [] occs decls (s:defs) structs

cCast ∷ C -> C -> C
cCast typ expr = parens ("*" <> parens (typ <> "*") <> parens ("&" <> expr))


cStructDef :: String -> C -> C
cStructDef name body = Code ("struct " <> n) [] [] [] [(n,stmt ("struct " <> lit n <> braces body))]
  where n = quoteVar name


instance Semigroup C where
  (Code c1 v1 d1 f1 s1) <> (Code c2 v2 d2 f2 s2) = Code (c1 <> c2) (v1 <> (v2 \\\ d1)) (d1 <> d2) (f1 <> f2) (s1 <> s2)
instance Monoid C where
  mempty = Code mempty mempty mempty mempty mempty

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
cleanStructs :: [(String,C)] -> [C]
cleanStructs = map snd . nubBy ((==) `on` fst) . reverse


cCall :: (Semigroup a, IsString a) => a -> [a] -> a
cCall x args = x <> parens (commas args)
