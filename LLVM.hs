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

--------------------------------
-- Helpers
stmts = mconcat . map stmt
stmt x = x <> "\n"
percent x = "%" <> x
num = lit . show

---------------------------------
-- Generation of LLVM types
ptr x = x <> "*"

struct :: [Type] -> C
struct fields = braces $ commas $ map vmtype fields

cFun :: String -> Type -> String -> C -> C
cFun n t arg env = "void " <> lit n <> "(" <> vmtype t <> " " <> lit arg <> "," <> env <> ")"

-- | Representation of a LL type
vmtype :: Type -> C
vmtype t0 = case t0 of
    (t :* u) -> struct [t,u]
    I -> struct []
    (Var x) -> percent (lit x)
    (Perp t) -> unkownCloType t <> " *"

-- | Function type when the env is unknown (thus a generic pointer)
unknownFunType = funType "i8"

-- | Function type getting an env and an arg
funType env t = ptr (cFun "" t "" (ptr env))

-- | Closure type when the environment is not known
unkownCloType = cloType "[0 x i8]"

-- | Representation of a closure
cloType env t = braces (commas [unknownFunType t, env])

typOf = vmtype . snd
dualTypOf = vmtype . dual . snd

-------------------
-- Variable helpers
dcl' :: (String, Type) -> C
dcl' = percent . dcl . fst
parameter (s,t) =  vmtype t <> " " <> dcl' (s,t)
var' (s,t) = vmtype t <> " " <> percent  (var (s,t))
coVar' (s,t) = vmtype (dual t) <> " " <> percent  (var (s,t))
lit' = percent . lit
tmp ∷ ∀ t. (String, t) → String → C
tmp (s,_) suff = "%" <> lit (quoteVar s) <> "_" <> lit suff


--------------------
-- Main work

-- | This function generates code to 'break into pieces' the environment which is
-- eliminated by the corresponding LL proof.
compile ∷ LL (String, Type) (String, Type) → C
compile t0 = case t0 of
  Tensor z x y t' ->
    stmts [dcl' x <> " = extractvalue " <> var' z <> ", 0\n"
          ,dcl' y <> " = extractvalue " <> var' z <> ", 1\n"] <>
    compile t'
  One _ t' -> "\n" <> compile t'
  Zero x -> stmt "call @abort()"
  Ax x y -> stmt (dcl' x <> "= add " <> var' y <> ", 0")

  Down z (x,t@(Perp u)) t' ->
    -- construct the argument to the closure (in 'x')
    cocompile t' <>
    -- call the closure:
    stmts
    [ -- find where the code (pointer) is
      tmp z "code_ptr" ~=~ "getelementptr " <> unkownCloType u <> ", " <> var' z <> ", i32 0, i32 0"
      -- read the code (pointer)
    , tmp z "code" ~=~ "load " <> unknownFunType u <> ", " <> unknownFunType u <> "* " <> tmp z "code_ptr"
      -- find the pointer to the env
    , tmp z "env " ~=~ "getelementptr " <> unkownCloType u <> ", " <> var' z <> ", i32 0, i32 1, i32 0"
      -- perform the call
    , "tail call void " <> tmp z "code" <> parens -- FIXME: should use musttail, but there is a bug in LLVM.
      (commas [vmtype u <+> "%" <> lit (quoteVar x), "i8* " <> tmp z "env"])
    , "ret void" ]


-- | Compiling negatives, by construction of the eliminated variable. Note that
-- we assume that the input proof is focused: thus there is a single (negative)
-- variable to eliminate. If we ever want to switch to eliminate (construct)
-- something else, we must 'wait'. That is, put the remainder of the code in a
-- continuation.
cocompile :: LL (String, Type) (String, Type) → C
cocompile t0 = case t0 of
  Ax x y -> stmt (dcl' x <> "= add " <> var' y <> ", 0")
  Par z x t' y u' ->
    cocompile t' <>
    cocompile u' <>
    tmp z "zero" ~=~ "insertvalue " <> dualTypOf z <> " undef, " <> coVar' x <> ", 0\n" <>
    dcl' z  ~=~ "insertvalue " <> dualTypOf z <> " " <> tmp z "zero" <> ", "  <> coVar' y  <> ",1\n"
  Bot z -> stmt ""
  Up z x@(xn,t) t' ->
     def ("define " <> cFun xfun t xnparam (ptr envStruct <+> "%env")<>
          braces (stmt mempty <>
                  -- load the environment into variables
                  mconcat [stmt (tmp v "ptr" <> " = getelementptr " <> envStruct <> ", " <>
                                                    ptr envStruct <+>  "%env, i32 0, i32 " <> num i) <>
                           stmt (dcl' v <> "= load " <> typOf v <> ", " <> ptr (typOf v) <+> tmp v "ptr")
                          | (v,i) <- zip env' [(0::Int)..]] <>
                  -- FIXME: here, free the *closure* that we entered
                  t'c )) <>

     stmts [tmp z "mem" <> " = call i8*" <+> cCall "@malloc" ["i64 666" {- FIXME -} ]
            -- allocate the closure
           ,tmp z "clo" <> " = bitcast i8* " <> tmp z "mem" <+> "to" <+> ptr cloTyp
            -- calculate the pointer to the code
           ,tmp z "code_0" ~=~ "getelementptr " <>  cloTyp <> ", " <> ptr cloTyp <+> tmp z "clo" <> ", i32 0, i32 0"
            -- cast it
           ,tmp z "code" ~=~ "bitcast " <> ptr unknownFunTyp <+> tmp z "code_0" <> " to " <> ptr funTyp
            -- write the pointer
           ,"store " <> funTyp <+> lit xfun <> ", " <> ptr funTyp <> tmp z "code"
           ] <>
     -- write the environment
     stmts (concat [[tmp v "ptr" <> " = getelementptr " <> cloTyp <> ", " <> ptr cloTyp <+> tmp z "clo" <> ", i32 0, i32 1, i32 " <> num i
                    ,"store " <>  var' v <> ", " <> ptr (typOf v) <+> tmp v "ptr"]
             | (v,i) <- zip env' [0..]]) <>
     stmt (dcl' z <> " = bitcast " <> ptr cloTyp <+> tmp z "clo" <> " to " <> dualTypOf z)
    where xfun = "@" ++ (quoteVar $ fresh xn "fun")
          t'c@(Code _ env _ _ _) = compile t'
          env' = nubBy ((==) `on` fst) (env \\\ [xn])
          envStruct = struct $ map snd env'
          cloTyp = cloType envStruct t
          unknownFunTyp = unknownFunType t
          funTyp = funType envStruct t
          xnparam = "%" ++ quoteVar xn

------------------
-- Top-level
compilTop ∷ ([(String, Type)], LL String String) → String
compilTop (ctx,input) = cCode $
  -- mconcat (cleanStructs (cStructs cctx <> cStructs t'c)) <>
  stmts ["%A = type i32"
        ,"%B = type i32"
        ,"declare noalias i8* @malloc(i64)"] <>
  lit (mconcat (fmap (<> "\n\n") (cDefs t'c))) <>
  ("define void @main_function(" <> cctx <> ") " <> braces t'c)
  where           t'c = compile t'
                  t' = (normalize ctx input)
                  cctx = commas [parameter x | x <- ctx]

main ∷ IO ()
main = writeFile "simp.ll" $ compilTop simpl
