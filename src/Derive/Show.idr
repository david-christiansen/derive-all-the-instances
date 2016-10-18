module Derive.Show

import Data.Vect

import Language.Reflection.Elab
import Language.Reflection.Utils
import Pruviloj.Core
import Pruviloj.Internals.TyConInfo
import Pruviloj.Internals

%access public export

isRType : Raw -> Bool
isRType RType = True
isRType _ = False



declareShow : (fam, sh : TTName) -> TyConInfo -> Elab TyDecl
declareShow fam eq info =
  do let paramArgs = map (\(n, t) => MkFunArg n t Implicit NotErased) (getParams info)
     constrs <- traverse
                     (\(n, t) =>
                        do n' <- gensym "constrarg"
                           pure $ MkFunArg n' `(Show ~(Var n)) Constraint NotErased) $
                     List.filter (isRType . snd) $
                     getParams info
     precn <- gensym "d"
     let precArg = with List [MkFunArg precn `(Prec) Explicit NotErased]
     arg <- applyTyCon (args info) (Var fam)
     pure $ Declare eq (paramArgs ++ constrs ++ precArg ++ arg) `(String)
  where
    makeImplicit : FunArg -> FunArg
    makeImplicit arg = record {plicity = Implicit} arg

    applyTyCon : List TyConArg -> Raw -> Elab (List FunArg)
    applyTyCon [] acc = pure $ [MkFunArg !(gensym "arg") acc Explicit NotErased]
    applyTyCon (TyConIndex arg :: args) acc =
        (\tl => makeImplicit arg :: tl) <$> applyTyCon args (RApp acc (Var (name arg)))
    applyTyCon (TyConParameter arg :: args) acc =
        applyTyCon args (RApp acc (Var (name arg)))

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
             (c : (TTName, List CtorArg, Raw)) -> Elab (FunClause Raw)
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
                                     True)
          solve
          -- We can find the argument positions by counting
          -- holes. Drop the constraints and indices, then take
          -- an arg
          focus !(unsafeNth (1 + length (getParams info) + (length (getIndices info))) holes')
          apply (Var arg) []; solve

          -- Now we get the actual arguments in place
          focus arg
          apply (mkApp (Var cn) (map (Var . name . ctorFunArg) ctorArgs)) []
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
        mkArgHole (CtorParameter _) = pure ()
        mkArgHole (CtorField arg) = do claim (name arg) (type arg)
                                       unfocus (name arg)

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
               if headName (type thisArg) == Just fam
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
                                          True)
                   solve
                   -- TC dict arguments to recursive call should be threaded through
                   traverse_
                     (\h => do ignore $ inHole h (resolveTC sh))
                     (List.take (length (getParams info)) hs)
                   prec <- unsafeNth (length (getParams info)) hs
                   focus prec; apply `(App : Prec) []; solve
                   field <- unsafeNth (1 + length (args info)) hs
                   ignore $ inHole field (apply (Var (name thisArg)) [] *> solve)

            useShow : Elab ()
            useShow =
                do -- call the real showArg
                   [tyH, dictH, xH] <- apply (Var `{showArg}) [True, True, True]
                   solve
                   focus xH; apply (Var (name thisArg)) []; solve
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
                showCtorArg' thisArg@(MkFunArg name _ Explicit NotErased) =
                    showOneArg thisArg
                showCtorArg' _ = skip

instClause : (sh, instn : TTName) ->
             (info : TyConInfo) ->
             (instArgs, instConstrs : List FunArg) ->
             Elab (List (FunClause Raw))
instClause sh instn info instArgs instConstrs =
  do let baseCtorN = SN (InstanceCtorN `{Show})
     (ctorN, _, _) <- lookupTyExact baseCtorN
     clause <- elabPatternClause
                 (do apply (Var instn)
                           (replicate (length instArgs +
                                       length instConstrs)
                                      True)
                     solve)
                 (do [ty, showImpl, showPrecImpl] <-
                        apply (Var ctorN) [True, False, False]
                     solve

                     -- ty was solved by unification, if things are going right
                     focus showImpl
                     shArg <- gensym "x"
                     attack; intro shArg
                     shPArgs <- apply (Var sh)
                                      (replicate (2 * length (getParams info) +
                                                  length (getIndices info) + 2)
                                                 True)
                     focus !(last shPArgs); apply (Var shArg) []; solve
                     traverse_ (\h => inHole h (exact `(Open : Prec) <|> resolveTC instn))
                               shPArgs
                     solve -- attack
                     solve -- the hole in the instance constructor

                     focus showPrecImpl
                     shPArgP <- gensym "d"
                     shPArgX <- gensym "x"
                     attack; intro shPArgP
                     attack; intro shPArgX
                     shPArgs' <- apply (Var sh)
                                       (replicate (2 * length (getParams info) +
                                                   length (getIndices info) + 2)
                                                  True)
                     focus !(last shPArgs'); apply (Var shPArgX) []; solve

                     focus !(unsafeNth (2 * length (getParams info) )
                                            shPArgs')
                     apply (Var shPArgP) []; solve
                     traverse_ (\h => inHole h (resolveTC instn)) shPArgs'
                     solve; solve -- attacks
                     solve) -- constructor hole



     pure [clause]


export
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
                                                     pure [MkFunArg constrn
                                                                      `(Show ~(Var n) : Type)
                                                                      Constraint
                                                                      NotErased]
                                    _ => pure [])
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
       pure ()
  where tcArgName : TyConArg -> TTName
        tcArgName (TyConParameter x) = name x
        tcArgName (TyConIndex x) = name x

        tcFunArg : TyConArg -> FunArg
        tcFunArg (TyConParameter x) = record {plicity = Implicit} x
        tcFunArg (TyConIndex x) = record {plicity = Implicit} x


