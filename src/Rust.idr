module Rust

import Compiler.ANF
import Compiler.Common
import Compiler.CompileExpr
import Data.String
import Data.Vect
import Idris.Syntax
import Libraries.Data.DList
import Runtime

data Counter : Type
data FuncArgCounts : Type
data IndentLevel : Type
data OutfileText : Type

incIndent : {auto _ : Ref IndentLevel Nat} -> Core ()
incIndent = update IndentLevel S

decIndent : {auto _ : Ref IndentLevel Nat} -> Core ()
decIndent = update IndentLevel pred

indent : {auto _ : Ref IndentLevel Nat} -> Core String
indent = do
  indentLevel <- get IndentLevel
  pure $ replicate (4 * indentLevel) ' '

emit' : {auto _ : Ref IndentLevel Nat}
     -> {auto _ : Ref OutfileText (DList String)}
     -> (line : String)
     -> (fc : String)
     -> Core ()
emit' line fc = update OutfileText $ flip snoc (!indent ++ line ++ fc)

emit : {auto _ : Ref IndentLevel Nat}
    -> {auto _ : Ref OutfileText (DList String)}
    -> FC
    -> (line : String)
    -> Core ()
emit EmptyFC line = emit' line ""
emit fc line = emit' line " // \{show fc}"

getTempVar : {auto _ : Ref Counter Nat} -> Core String
getTempVar = do
  i <- get Counter
  put Counter (S i)
  pure "temp_\{show i}"

toRustAVar : AVar -> String
toRustAVar (ALocal i) = "var_\{show i}"
toRustAVar ANull = assert_total $ idris_crash "[TODO] toRustAVar ANull"

buildList : List String -> String
buildList = fastConcat . intersperse ", "

buildArgsList : List AVar -> String
buildArgsList args = buildList $ map (\arg => "\{toRustAVar arg}.clone()") args

toRustName : Name -> String
toRustName n = fastConcat $ map clean (unpack $ toRustName' n)
  where
    toRustName' : Name -> String
    toRustName' n = case n of
      (NS ns n) => "\{show ns}_\{toRustName' n}"
      (UN (Basic s)) => s
      (UN (Field s)) => s
      (UN Underscore) => "_"
      (MN s i) => "\{s}_\{show i}"
      -- PV : Name -> Int -> Name -- pattern variable name; int is the resolved function id
      (PV a b) => assert_total $ idris_crash "[TODO] toRustName PV: \{show a} - \{show b}"
      (DN _ n) => toRustName' n
      -- Nested : (Int, Int) -> Name -> Name -- nested function name
      (Nested a b) => assert_total $ idris_crash "[TODO] toRustName Nested: \{show a} - \{show b}"
      -- CaseBlock : String -> Int -> Name -- case block nested in (resolved) name
      (CaseBlock a b) => assert_total $ idris_crash "[TODO] toRustName CaseBlock: \{show a} - \{show b}"
      -- WithBlock : String -> Int -> Name -- with block nested in (resolved) name
      (WithBlock a b) => assert_total $ idris_crash "[TODO] toRustName WithBlock: \{show a} - \{show b}"
      -- Resolved : Int -> Name -- resolved, index into context
      (Resolved a) => assert_total $ idris_crash "[TODO] toRustName Resolved: \{show a}"

    clean : Char -> String
    clean ch = case ch of
      '{' => "_lbrace_"
      '}' => "_rbrace_"
      ':' => "_colon_"
      '.' => "_dot_"
      '=' => "_eq_"
      '<' => "_lt_"
      c => singleton c

toRustPrimFn : PrimFn _ -> (argsList : String) -> String
toRustPrimFn f argsList = case f of
  (Add ty) => assert_total $ idris_crash "[TODO] toRustPrimFn Add \{show ty}"
  (Sub ty) => "idris_sub_\{show ty}(\{argsList})"
  (Mul ty) => assert_total $ idris_crash "[TODO] toRustPrimFn Mul \{show ty}"
  (Div ty) => assert_total $ idris_crash "[TODO] toRustPrimFn Div \{show ty}"
  (Mod ty) => assert_total $ idris_crash "[TODO] toRustPrimFn Mod \{show ty}"
  (Neg ty) => assert_total $ idris_crash "[TODO] toRustPrimFn Neg \{show ty}"
  (ShiftL ty) => assert_total $ idris_crash "[TODO] toRustPrimFn ShiftL \{show ty}"
  (ShiftR ty) => assert_total $ idris_crash "[TODO] toRustPrimFn ShiftR \{show ty}"
  (BAnd ty) => assert_total $ idris_crash "[TODO] toRustPrimFn BAnd \{show ty}"
  (BOr ty) => assert_total $ idris_crash "[TODO] toRustPrimFn BOr \{show ty}"
  (BXOr ty) => assert_total $ idris_crash "[TODO] toRustPrimFn BXOr \{show ty}"
  (LT ty) => "idris_lt_\{show ty}(\{argsList})"
  (LTE ty) => "idris_lte_\{show ty}(\{argsList})"
  (EQ ty) => "idris_eq_\{show ty}(\{argsList})"
  (GTE ty) => assert_total $ idris_crash "[TODO] toRustPrimFn GTE \{show ty}"
  (GT ty) => assert_total $ idris_crash "[TODO] toRustPrimFn GT \{show ty}"
  StrLength => assert_total $ idris_crash "[TODO] toRustPrimFn StrLength"
  StrHead => assert_total $ idris_crash "[TODO] toRustPrimFn StrHead"
  StrTail => assert_total $ idris_crash "[TODO] toRustPrimFn StrTail"
  StrIndex => assert_total $ idris_crash "[TODO] toRustPrimFn StrIndex"
  StrCons => assert_total $ idris_crash "[TODO] toRustPrimFn StrCons"
  StrAppend => assert_total $ idris_crash "[TODO] toRustPrimFn StrAppend"
  StrReverse => assert_total $ idris_crash "[TODO] toRustPrimFn StrReverse"
  StrSubstr => assert_total $ idris_crash "[TODO] toRustPrimFn StrSubstr"
  DoubleExp => assert_total $ idris_crash "[TODO] toRustPrimFn DoubleExp"
  DoubleLog => assert_total $ idris_crash "[TODO] toRustPrimFn DoubleLog"
  DoublePow => assert_total $ idris_crash "[TODO] toRustPrimFn DoublePow"
  DoubleSin => assert_total $ idris_crash "[TODO] toRustPrimFn DoubleSin"
  DoubleCos => assert_total $ idris_crash "[TODO] toRustPrimFn DoubleCos"
  DoubleTan => assert_total $ idris_crash "[TODO] toRustPrimFn DoubleTan"
  DoubleASin => assert_total $ idris_crash "[TODO] toRustPrimFn DoubleASin"
  DoubleACos => assert_total $ idris_crash "[TODO] toRustPrimFn DoubleACos"
  DoubleATan => assert_total $ idris_crash "[TODO] toRustPrimFn DoubleATan"
  DoubleSqrt => assert_total $ idris_crash "[TODO] toRustPrimFn DoubleSqrt"
  DoubleFloor => assert_total $ idris_crash "[TODO] toRustPrimFn DoubleFloor"
  DoubleCeiling => assert_total $ idris_crash "[TODO] toRustPrimFn DoubleCeiling"
  (Cast a b) => assert_total $ idris_crash "[TODO] toRustPrimFn Cast \{show a} \{show b}"
  BelieveMe => assert_total $ idris_crash "[TODO] toRustPrimFn BelieveMe"
  Crash => assert_total $ idris_crash "[TODO] toRustPrimFn Crash"

toRustConstant : Constant -> String
toRustConstant k = case k of
  (I k) => "Value::Int(\{show k})"
  (I8 k) => "Value::Int(\{show k})"
  (I16 k) => "Value::Int(\{show k})"
  (I32 k) => "Value::Int(\{show k})"
  (I64 k) => "Value::Int(\{show k})"
  (BI k) => "Value::Int(\{show k})"
  (B8 k) => "Value::Int(\{show k})"
  (B16 k) => "Value::Int(\{show k})"
  (B32 k) => "Value::Int(\{show k})"
  (B64 k) => "Value::Int(\{show k})"
  (Str k) => "Value::Str(String::from(\{show k}))"
  (Ch k) => "Value::Ch(\{show k})"
  (Db k) => "Value::Db(\{show k})"
  (PrT k) => "Value::PrT(PrimType::\{show k})"
  WorldVal => "Value::WorldVal"

pack : (var : String) -> CFType -> String
pack var ty = case ty of
  CFUnit => "Value::Unit"
  CFInt => assert_total $ idris_crash "[TODO] pack CFInt"
  CFInteger => assert_total $ idris_crash "[TODO] pack CFInteger"
  CFInt8 => assert_total $ idris_crash "[TODO] pack CFInt8"
  CFInt16 => assert_total $ idris_crash "[TODO] pack CFInt16"
  CFInt32 => assert_total $ idris_crash "[TODO] pack CFInt32"
  CFInt64 => assert_total $ idris_crash "[TODO] pack CFInt64"
  CFUnsigned8 => assert_total $ idris_crash "[TODO] pack CFUnsigned8"
  CFUnsigned16 => assert_total $ idris_crash "[TODO] pack CFUnsigned16"
  CFUnsigned32 => assert_total $ idris_crash "[TODO] pack CFUnsigned32"
  CFUnsigned64 => assert_total $ idris_crash "[TODO] pack CFUnsigned64"
  CFString => assert_total $ idris_crash "[TODO] pack CFString"
  CFDouble => assert_total $ idris_crash "[TODO] pack CFDouble"
  CFChar => assert_total $ idris_crash "[TODO] pack CFChar"
  CFPtr => assert_total $ idris_crash "[TODO] pack CFPtr"
  CFGCPtr => assert_total $ idris_crash "[TODO] pack CFGCPtr"
  CFBuffer => assert_total $ idris_crash "[TODO] pack CFBuffer"
  CFForeignObj => assert_total $ idris_crash "[TODO] pack CFForeignObj"
  CFWorld => assert_total $ idris_crash "[TODO] pack CFWorld"
  (CFFun a b) => assert_total $ idris_crash "[TODO] pack CFFun \{show a} \{show b}"
  (CFIORes ty) => pack var ty
  (CFStruct a b) => assert_total $ idris_crash "[TODO] pack CFStruct \{show a} \{show b}"
  (CFUser a b) => assert_total $ idris_crash "[TODO] pack CFUser \{show a} \{show b}"

unpack : (var : String) -> CFType -> String
unpack var ty = case ty of
  CFUnit => assert_total $ idris_crash "[TODO] unpack CFUnit"
  CFInt => assert_total $ idris_crash "[TODO] unpack CFInt"
  CFInteger => assert_total $ idris_crash "[TODO] unpack CFInteger"
  CFInt8 => assert_total $ idris_crash "[TODO] unpack CFInt8"
  CFInt16 => assert_total $ idris_crash "[TODO] unpack CFInt16"
  CFInt32 => assert_total $ idris_crash "[TODO] unpack CFInt32"
  CFInt64 => assert_total $ idris_crash "[TODO] unpack CFInt64"
  CFUnsigned8 => assert_total $ idris_crash "[TODO] unpack CFUnsigned8"
  CFUnsigned16 => assert_total $ idris_crash "[TODO] unpack CFUnsigned16"
  CFUnsigned32 => assert_total $ idris_crash "[TODO] unpack CFUnsigned32"
  CFUnsigned64 => assert_total $ idris_crash "[TODO] unpack CFUnsigned64"
  CFString => "{ let Value::Str(v) = \{var} else { unreachable!(); }; v }"
  CFDouble => assert_total $ idris_crash "[TODO] unpack CFDouble"
  CFChar => assert_total $ idris_crash "[TODO] unpack CFChar"
  CFPtr => assert_total $ idris_crash "[TODO] unpack CFPtr"
  CFGCPtr => assert_total $ idris_crash "[TODO] unpack CFGCPtr"
  CFBuffer => assert_total $ idris_crash "[TODO] unpack CFBuffer"
  CFForeignObj => assert_total $ idris_crash "[TODO] unpack CFForeignObj"
  CFWorld => assert_total $ idris_crash "[TODO] unpack CFWorld"
  (CFFun a b) => assert_total $ idris_crash "[TODO] unpack CFFun \{show a} \{show b}"
  (CFIORes a) => assert_total $ idris_crash "[TODO] unpack CFIORes \{show a}"
  (CFStruct a b) => assert_total $ idris_crash "[TODO] unpack CFStruct \{show a} \{show b}"
  (CFUser a b) => assert_total $ idris_crash "[TODO] unpack CFUser \{show a} \{show b}"

buildExpr : {auto _ : Ref Counter Nat}
         -> {auto _ : Ref OutfileText (DList String)}
         -> {auto _ : Ref IndentLevel Nat}
         -> ANF
         -> Core String

buildExpr (AV _ var) = pure $ toRustAVar var

buildExpr (AAppName _ _ n args) = pure "\{toRustName n}(\{buildArgsList args})"

buildExpr (AUnderApp _ n missing args) = pure "Value::Fun(\"\{toRustName n}\", vec![\{buildArgsList args}], \{show missing})"

buildExpr (AApp _ _ closure arg) = pure "apply_fun(\{toRustAVar closure}.clone(), \{toRustAVar arg}.clone())"

buildExpr (ALet fc var val body) = do
  emit fc "let var_\{show var} = \{!(buildExpr val)};"
  buildExpr body

buildExpr (ACon _ n _ tag args) = pure $ case tag of
                                          Just tag => "Value::Con(Some(\{show tag}), vec![\{buildArgsList args}])"
                                          Nothing => "Value::Con(None, vec![\{buildArgsList args}])"

buildExpr (AOp _ _ primFn args) = pure $ toRustPrimFn primFn (buildArgsList $ toList args)

buildExpr (AExtPrim _ _ n args) = assert_total $ idris_crash "[TODO] AExtPrim \{show n}"

buildExpr (AConCase fc var alts deft) = do
  let rvar = toRustAVar var
  retVar <- getTempVar
  emit fc "let Value::Con(\{rvar}_tag, \{rvar}_args) = \{rvar} else { unreachable!(); };"
  emit emptyFC "let \{retVar} = match \{rvar}_tag {"
  incIndent
  traverse_ (buildAlt rvar) alts
  case deft of
    Just body => do
      emit emptyFC "_ => {"
      incIndent
      emit emptyFC !(buildExpr body)
      decIndent
      emit emptyFC "}"
    Nothing => emit emptyFC "_ => unreachable!(),"
  decIndent
  emit emptyFC "};"
  pure retVar
    where
      buildAlt : (rvar : String) -> AConAlt -> Core ()
      buildAlt rvar (MkAConAlt n _ tag args body) = do
        case tag of
          Just tag => emit emptyFC "Some(\{show tag}) /* \{show n} */ => {"
          Nothing => emit emptyFC "None /* \{show n} */ => {"
        incIndent
        traverse_
          (\(i, arg) => emit emptyFC "let var_\{show arg} = \{rvar}_args[\{show i}].clone();")
          (zip [0..length args] args)
        emit emptyFC !(buildExpr body)
        decIndent
        emit emptyFC "}"

buildExpr (AConstCase fc var alts deft) = do
  retVar <- getTempVar
  emit fc "let \{retVar} = match \{toRustAVar var} {"
  incIndent
  traverse_
    (
      \(MkAConstAlt k body) => do
        emit emptyFC "\{toRustConstant k} => {"
        incIndent
        emit emptyFC !(buildExpr body)
        decIndent
        emit emptyFC "}"
    )
    alts
  case deft of
    Just body => do
      emit emptyFC "_ => {"
      incIndent
      emit emptyFC !(buildExpr body)
      decIndent
      emit emptyFC "}"
    Nothing => emit emptyFC "_ => unreachable!(),"
  decIndent
  emit emptyFC "};"
  pure retVar

buildExpr (APrimVal _ k) = pure $ toRustConstant k

buildExpr (AErased _) = assert_total $ idris_crash "[TODO] buildExpr AErased"

buildExpr (ACrash _ a) = assert_total $ idris_crash "[TODO] buildExpr ACrash \{a}"

buildDef : {auto _ : Ref Counter Nat}
        -> {auto _ : Ref FuncArgCounts (List (String, Nat))}
        -> {auto _ : Ref IndentLevel Nat}
        -> {auto _ : Ref OutfileText (DList String)}
        -> Name
        -> ANFDef
        -> Core ()

buildDef n (MkAFun args body) = do
  let rn = toRustName n
  let nargs = length args
  update FuncArgCounts $ \defs => (rn, nargs) :: defs
  let args_list = buildList $ map (\i => "var_\{show i}: Value") args
  emit EmptyFC "fn \{rn}(\{args_list}) -> Value {"
  incIndent
  emit EmptyFC !(buildExpr body)
  decIndent
  emit EmptyFC "}\n"
  pure ()

buildDef n (MkACon tag arity nt) = pure ()

buildDef n (MkAForeign ccs argTys retTy) = do
  let rn = toRustName n
  let nargs = length argTys
  update FuncArgCounts $ \defs => (rn, nargs) :: defs
  let fn = case show n of
            "Prelude.IO.prim__putStr" => "idris_\{rn}"
            _ => case parseCC ["rust"] ccs of
                  Just (_, fn :: _) => fn
                  _ => assert_total $ idris_crash "Unknown foreign function `\{show n}`"
  let args = buildArgs nargs
  let argList = buildList $ map (\a => "\{a}: Value") args
  emit EmptyFC "fn \{rn}(\{argList}) -> Value {"
  incIndent
  let argList = case retTy of
                  CFIORes _ => unpackArgs (init' $ zip args argTys)
                  _ => unpackArgs (zip args argTys)
  emit EmptyFC "let val = \{fn}(\{argList});"
  emit EmptyFC $ pack "val" retTy
  decIndent
  emit EmptyFC "}\n"
    where
      buildArgs : Nat -> List String
      buildArgs Z = []
      buildArgs (S k) = map (\i => "var_\{show i}") [0..k]

      unpackArgs : List (String, CFType) -> String
      unpackArgs args = buildList $ map (\(arg, ty) => unpack arg ty) args

      init' : List a -> List a
      init' [] = []
      init' xs@(_ :: _) = init xs

buildDef n (MkAError err) = assert_total $ idris_crash "\{show n}: \{show err}"

buildFile : List (Name, ANFDef) -> (outfile : String) -> Core ()
buildFile defs outfile = do
  _ <- newRef Counter 0
  _ <- newRef FuncArgCounts []
  _ <- newRef IndentLevel 0
  _ <- newRef OutfileText DList.Nil
  traverse_ (uncurry buildDef) defs
  let clauses = map buildFuncClause !(get FuncArgCounts)
  update OutfileText ("""
  fn apply_fun(mut fun: Value, arg: Value) -> Value {
      let Value::Fun(name, mut args, mut missing) = fun else { unreachable!(); };
      args.push(arg);
      missing -= 1;
      fun = Value::Fun(name, args, missing);
      while let Value::Fun(name, args, 0) = fun {
          fun = match name {
              \{fastConcat $ intersperse "\n            " clauses}
              _ => unreachable!(),
          }
      }
      fun
  }

  """ ::)
  update OutfileText (runtime ::)
  let file = fastConcat $ intersperse "\n" (reify !(get OutfileText))
  writeFile outfile file
    where
      buildFuncClause : (String, Nat) -> String
      buildFuncClause (f, Z) = "\"\{f}\" => \{f}(),"
      buildFuncClause (f, (S k)) = "\"\{f}\" => \{f}(\{args}),"
        where
          args = buildList $ map (\n => "args[\{show n}].clone()") [0..k]

compileExpr : Ref Ctxt Defs
           -> Ref Syn SyntaxInfo
           -> (tmpDir : String)
           -> (outputDir : String)
           -> ClosedTerm
           -> (outfile : String)
           -> Core (Maybe String)
compileExpr _ _ _ _ ct outfile = do
  cdata <- getCompileData False ANF ct
  let defs = anf cdata
  buildFile defs outfile
  pure $ Just outfile

executeExpr : Ref Ctxt Defs
           -> Ref Syn SyntaxInfo
           -> (tmpDir : String)
           -> ClosedTerm
           -> Core ()
executeExpr _ _ _ _ = coreLift $ putStrLn "Expression execution is not implemented"

export
rustCodegen : Codegen
rustCodegen = MkCG compileExpr executeExpr Nothing Nothing
