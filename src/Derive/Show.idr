module Derive.Show

import Data.Vect

import Language.Reflection.Elab
import Language.Reflection.Utils
import Derive.Kit
import Derive.Util.TyConInfo
%access public


declareShow : (fam, sh : TTName) -> TyConInfo -> Elab TyDecl
declareShow fam eq info =
  do let paramArgs = map (\(n, t) => MkFunArg n t Implicit NotErased) (getParams info)
     constrs <- traverse
                     (\(n, t) =>
                        do n' <- gensym "constrarg"
                           return $ MkFunArg n' `(Show ~(Var n)) Constraint NotErased) $
                     filter (isRType . snd) $
                     getParams info
     precn <- gensym "d"
     let precArg = with List [MkFunArg precn `(Prec) Explicit NotErased]
     arg <- applyTyCon (args info) (Var fam)
     return $ Declare eq (paramArgs ++ constrs ++ precArg ++ arg) `(String)
  where
    makeImplicit : FunArg -> FunArg
    makeImplicit arg = record {plicity = Implicit} arg

    applyTyCon : List TyConArg -> Raw -> Elab (List FunArg)
    applyTyCon [] acc = return $ [MkFunArg !(gensym "arg") acc Explicit NotErased]
    applyTyCon (TyConIndex arg :: args) acc =
        (\tl => makeImplicit arg :: tl) <$> applyTyCon args (RApp acc (Var (argName arg)))
    applyTyCon (TyConParameter arg :: args) acc =
        applyTyCon args (RApp acc (Var (argName arg)))

    getFunArg : TyConArg -> FunArg
    getFunArg (TyConParameter x) = makeImplicit x
    getFunArg (TyConIndex x)     = makeImplicit x

    mkArg : TTName -> Raw -> FunArg
    mkArg n t = MkFunArg n t Explicit NotErased

||| Compute the constructor name's representation in user output
strName : TTName -> String
strName (UN n) = case unpack n of
                   [] => ""
                   (c :: cs) => if isAlpha c then n else "(" ++ n ++ ")"
strName (NS n _) = strName n
strName (MN x y) = y
strName (SN x) = "**SN**" -- won't happen with user-declared types
strName NErased = "**Erased**" -- won't happen with user-declared types

||| Make the show clause for a single constructor
ctorClause : (fam, sh : TTName) -> (info : TyConInfo) ->
             (c : (TTName, List CtorArg, Raw)) -> Elab FunClause
ctorClause fam sh info ctor =
  do -- Begin by making non-param names unique (so we can use them for holes as well)
    (cn, ctorArgs, resTy) <- processCtorArgs info ctor
    elabPatternClause
      (do -- First give consistent bindings to the parameters
          traverse {b=()} (\(n, ty) => do claim n ty ; unfocus n) (getParams info)
          -- Next create holes for arguments - do indices, then a hole for each actual arg
          -- Now make holes for non-param args
          traverse mkArgHole ctorArgs

          -- Now make a hole for the argument itself
          arg <- newHole "arg" resTy

          -- Now apply show, with holes for its args that we will fill
          -- with these ones. Most will be solved through unification,
          -- but not all.
          holes' <- apply (mkApp (Var sh) (map (Var . fst) (getParams info)))
                          (replicate (length (getParams info) +
                                      length (getIndices info) + 2)
                                     (True, 0))
          solve
          -- We can find the argument positions by counting
          -- holes. Drop the constraints and indices, then take
          -- an arg
          focus (snd !(unsafeNth (1 + length (getParams info) + (length (getIndices info))) holes'))
          apply (Var arg) []; solve

          -- Now we get the actual arguments in place
          focus arg
          apply (mkApp (Var cn) (map (Var . argName . ctorFunArg) ctorArgs)) []
          solve)
      (if hasArgsToShow ctorArgs
         then do d <- newHole "d" `(Prec)
                 shownArgs <- newHole "args" `(String)
                 fill `(showCon ~(Var d) ~(RConstant (Str (strName cn))) ~(Var shownArgs)); solve
                 focus d; search
                 focus shownArgs
                 traverse_ showCtorArg ctorArgs
                 -- leaves behind a hole waiting for the last arg string - we just fill with ""
                 fill `(""); solve
         else do fill (RConstant (Str (strName cn))); solve)

  where mkArgHole : CtorArg -> Elab ()
        mkArgHole (CtorParameter _) = return ()
        mkArgHole (CtorField arg) = do claim (argName arg) (argTy arg)
                                       unfocus (argName arg)

        ctorFunArg : CtorArg -> FunArg
        ctorFunArg (CtorParameter a) = a
        ctorFunArg (CtorField a) = a


        showOneArg : FunArg -> Elab ()
        showOneArg thisArg =
            do argHere <- newHole "thisArg" `(String)
               rest <- newHole "next" `(String)
               fill `(~(Var argHere) ++ ~(Var rest) : String)
               solve
               focus argHere
               if headVar (argTy thisArg) == Just fam
                 then recursiveCall
                 else useShow
               focus rest
          where
            recursiveCall : Elab ()
            recursiveCall =
                do -- recursive call to self with initial space
                   afterSpace <- newHole "afterSpace" `(String)
                   fill `(" " ++ ~(Var afterSpace)); solve
                   focus afterSpace

                   hs <- apply (mkApp (Var sh) (map (Var . fst) (getParams info)))
                               (replicate (length (getParams info) +
                                           length (getIndices info)
                                           + 2)
                                          (True, 0))
                   solve
                   -- TC dict arguments to recursive call should be threaded through
                   traverse_
                     (\h => do inHole (snd h) (resolveTC sh))
                     (List.take (length (getParams info)) hs)
                   prec <- snd <$> unsafeNth (length (getParams info)) hs
                   focus prec; apply `(App : Prec) []; solve
                   field <- snd <$> unsafeNth (1 + length (args info)) hs
                   inHole field (apply (Var (argName thisArg)) [] *> solve)

            useShow : Elab ()
            useShow =
                do -- call the real showArg
                   [(_, tyH), (_, dictH), (_, xH)] <- apply (Var `{showArg}) [(True, 0), (True, 0), (True, 0)]
                   solve
                   focus xH; apply (Var (argName thisArg)) []; solve
                   focus dictH; resolveTC sh



        hasArgsToShow : List CtorArg -> Bool
        hasArgsToShow [] = False
        hasArgsToShow (CtorParameter (MkFunArg _ _ Explicit _) :: _) = True
        hasArgsToShow (CtorField (MkFunArg _ _ Explicit _) :: _) = True
        hasArgsToShow (_ :: args) = hasArgsToShow args

        showCtorArg : CtorArg -> Elab ()
        showCtorArg ca = case ca of
                           CtorParameter a => showCtorArg' a
                           CtorField a => showCtorArg' a
          where showCtorArg' : FunArg -> Elab ()
                showCtorArg' (MkFunArg _ RType Explicit _) =
                    do h <- newHole "next" `(String)
                       fill `(" _" ++ ~(Var h) : String); solve
                       focus h
                showCtorArg' (MkFunArg _ _ Explicit Erased) =
                    do h <- newHole "next" `(String)
                       fill `(" _" ++ ~(Var h) : String); solve
                       focus h
                showCtorArg' thisArg@(MkFunArg argName _ Explicit NotErased) =
                    showOneArg thisArg
                showCtorArg' _ = skip

instClause : (sh, instn : TTName) ->
             (info : TyConInfo) ->
             (instArgs, instConstrs : List FunArg) ->
             Elab (List FunClause)
instClause sh instn info instArgs instConstrs =
  do let baseCtorN = SN (InstanceCtorN `{Show})
     (ctorN, _, _) <- lookupTyExact baseCtorN
     clause <- elabPatternClause
                 (do apply (Var instn)
                           (replicate (length instArgs +
                                       length instConstrs)
                                      (True, 0))
                     solve)
                 (do [(_, ty), (_, showImpl), (_, showPrecImpl)] <-
                        apply (Var ctorN) [(True, 0), (False, 0), (False, 0)]
                     solve

                     -- ty was solved by unification, if things are going right
                     focus showImpl
                     shArg <- gensym "x"
                     attack; intro (Just shArg)
                     shPArgs <- apply (Var sh)
                                      (replicate (2 * length (getParams info) +
                                                  length (getIndices info) + 2)
                                                 (True, 0))
                     focus (snd !(last shPArgs)); apply (Var shArg) []; solve
                     traverse_ (\h => inHole (snd h) (exact `(Open : Prec) <|> resolveTC instn))
                               shPArgs
                     solve -- attack
                     solve -- the hole in the instance constructor

                     focus showPrecImpl
                     shPArgP <- gensym "d"
                     shPArgX <- gensym "x"
                     attack; intro (Just shPArgP)
                     attack; intro (Just shPArgX)
                     shPArgs' <- apply (Var sh)
                                       (replicate (2 * length (getParams info) +
                                                   length (getIndices info) + 2)
                                                  (True, 0))
                     focus (snd !(last shPArgs')); apply (Var shPArgX) []; solve

                     focus (snd !(unsafeNth (2 * length (getParams info) )
                                            shPArgs'))
                     apply (Var shPArgP) []; solve
                     traverse_ (\h => inHole (snd h) (resolveTC instn)) shPArgs'
                     solve; solve -- attacks
                     solve) -- constructor hole



     return [clause]


abstract
deriveShow : (fam : TTName) -> Elab ()
deriveShow fam =
    do sh <- flip NS !currentNamespace . SN . MetaN fam <$> gensym "showImpl"
       datatype <- lookupDatatypeExact fam
       info <- getTyConInfo (tyConArgs datatype) (tyConRes datatype)
       decl <- declareShow fam sh info
       declareType decl
       let instn = NS (SN $ InstanceN `{Show} [show fam]) !currentNamespace
       instConstrs <- Foldable.concat <$>
                      traverse (\ param =>
                                  case param of
                                    (n, RType) => do constrn <- gensym "instarg"
                                                     return [MkFunArg constrn
                                                                      `(Show ~(Var n) : Type)
                                                                      Constraint
                                                                      NotErased]
                                    _ => return [])
                               (getParams info)
       let instArgs = map tcFunArg (args info)
       let instRes = RApp (Var `{Show})
                          (mkApp (Var fam)
                                 (map (Var . tcArgName) (args info)))
       declareType $ Declare instn (instArgs ++ instConstrs) instRes
       clauses <- traverse (ctorClause fam sh info) (constructors datatype)
       defineFunction $ DefineFun sh clauses
       defineFunction $
         DefineFun instn !(instClause sh instn info instArgs instConstrs)
       addInstance `{Show} instn
       return ()
  where tcArgName : TyConArg -> TTName
        tcArgName (TyConParameter x) = argName x
        tcArgName (TyConIndex x) = argName x

        tcFunArg : TyConArg -> FunArg
        tcFunArg (TyConParameter x) = record {plicity = Implicit} x
        tcFunArg (TyConIndex x) = record {plicity = Implicit} x


namespace TestDecls
  -- Can't derive Eq for this one!
  data SimpleFun a b = MkSimpleFun (a -> b)

  data MyNat = MyZ | MyS MyNat

  data MyList a = Nil | (::) a (MyList a)

  namespace V
    data MyVect : MyNat -> Type -> Type where
      Nil : MyVect MyZ a
      (::) : a -> MyVect n a -> MyVect (MyS n) a

  -- All elements of this should be Eq, because it's for runtime and the Nat is erased
  data CompileTimeNat : Type where
    MkCTN : .(n : Nat) -> CompileTimeNat

decl syntax derive Show for {n} = %runElab (deriveShow `{n})

derive Show for MyNat
derive Show for MyList
derive Show for MyVect
derive Show for CompileTimeNat


namespace Tests
  test1 : show (with V [1,2,3]) = "(::) 1 ((::) 2 ((::) 3 Nil))"
  test1 = Refl
  
  test2 : show (MyS (MyS MyZ)) = "MyS (MyS MyZ)"
  test2 = Refl
  
  test3 : show (the (MyVect _ Integer) [1,2,3]) = show (the (MyList Integer) [1,2,3])
  test3 = Refl
  
  test4 : show (MkCTN 45) = "MkCTN _"
  test4 = Refl
