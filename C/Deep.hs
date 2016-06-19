-- | Compile a focused, polarised logic into C.
compileC ∷ LL (String, Type) (String, Type) → C
compileC t0 = case t0 of
  Tensor z x y t' ->
    cDecl' x <> " = " <> var z <> ".fst;\n" <>
    cDecl' y <> " = " <> var z <> ".snd;\n" <>
    compileC t'
  One _ t' -> "NOP();\n" <> compileC t'
  Zero x -> "ABORT(" <> var x <> ");\n"
  Ax x y -> stmt (coDecl x <> "=" <> var y)

  Down z (x,_) t' ->
    cocompileC t' <>
    var z <> "->code" <> parens (commas [lit (quoteVar x),var z <> "->env"]) <> ";\n"

-- | Compiling negatives, by construction of the eliminated variable.
cocompileC :: LL (String, Type) (String, Type) → C
cocompileC t0 = case t0 of
  Ax x y -> stmt (coDecl x <> "=" <> var y)
  Par z x t' y u' ->
    cocompileC t' <>
    cocompileC u' <>
    coDecl z <> " = " <> braces (".fst = " <> var x <> ",\n.snd = " <> var y) <> ";\n"
  Bot z -> stmt (cDecl' z <> " = {}")
  Up z x@(xn,t) t' ->
     cFun (envStruct <> "* env") t (Just xn) xfun <>
     braces (mconcat [stmt (cDecl' v <> "= env->" <> var v) | v <- env'] <>
             t'c )<> -- FIXME: hoist to the top level.
     stmt (coDecl z <> " = " <> cCall "malloc" ["4 /* fixme */+" <>  cCall "sizeof" [envStruct]]) <>
     stmt (envStruct <> " " <> cXenv <> " = " <> braces (commas $ map var env')) <>
     stmt (var z <> "->code = " <> lit xfun) <> -- fixme: add a cast
     stmt (cCall "memcpy" [var z <> "->env ","&" <> cXenv,cCall "sizeof" [cXenv]])
    where xenv = (xn ++ "_env")
          xfun = quoteVar $ fresh xn "fun"
          t'c@(Code _ env _ _ _) = compileC t'
          env' = nubBy ((==) `on` fst) (env \\\ [xn])
          envStruct = cStructDef (cEnvName env') (cStruct env')
          cXenv = lit (quoteVar xenv)


cDecl :: Type -> Maybe String -> C
cDecl t0 n = case t0 of
    (t :* u) -> cStructDef (cTypeName t0) (cStruct [("fst",t),("snd",u)]) <+> cName n
    I -> cStructDef (cTypeName t0) (cStruct []) <+> cName n
    (Var x) -> lit x <> " " <> cName n
    (Perp t) -> cStructDef (cTypeName t0)
                  (cFun "char*" t Nothing "(*code)" <> ";\n" <>
                   "char env[0];") <> "*" <+> cName n

cTypeName :: Type -> String
cTypeName (t :* u) = "p" <> cTypeName t <> "_" <> cTypeName u
cTypeName (I) = "i"
cTypeName (Var x) = "v" <> x
cTypeName (Perp t) = "n" <> cTypeName t

cEnvName :: [(String,Type)] -> String
cEnvName env = "e" <> mconcat ["f_" <> f <> "_" <> cTypeName t | (f,t) <- env]

cFun :: C -> Type -> Maybe String -> String -> C
cFun env t arg n = "void " <> lit n <> "(" <> cDecl t arg <> "," <> env <> ")"

-- cFun "void " <> parens("*" <> nn) <> parens (cDecl x Nothing)

cDecl0 t = cDecl t Nothing

coDecl (n,t) = cDecl (dual t) (Just n)
cDecl' (n,t) = cDecl t (Just n)

cStruct :: [(String,Type)] -> C
cStruct fields = (mconcat [cDecl' (f,t) <> ";\n" | (f,t) <- fields])

cName ∷ Maybe String → C
cName (Just x) = dcl x
cName Nothing = ""

cCall x args = x <> parens (commas args)
