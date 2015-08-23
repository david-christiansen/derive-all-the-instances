module Derive.Eq

import Data.Vect

import Language.Reflection.Elab
import Language.Reflection.Utils
import Derive.Util.TyConInfo
import Derive.Kit

%access private

||| Declare the underlying == function
declareEq : (fam, eq : TTName) -> (info : TyConInfo) -> Elab TyDecl
declareEq fam eq info =
    do let paramArgs = map (\(n, t) => MkFunArg n t Implicit NotErased) (getParams info)

       constrs <- traverse
                     (\(n, t) =>
                        do n' <- gensym "constrarg"
                           return $ MkFunArg n' `(Eq ~(Var n)) Constraint NotErased) $
                     filter (isRType . snd) $
                     getParams info
       arg1 <- applyTyCon (args info) (Var fam)
       arg2 <- applyTyCon (args info) (Var fam)
       return $ Declare eq (paramArgs ++ constrs ++ arg1 ++ arg2) `(Bool)
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



||| Make the matching clause for a single constructor
ctorClause : (fam, eq : TTName) -> (info : TyConInfo) ->
             (c : (TTName, List CtorArg, Raw)) -> Elab FunClause
ctorClause fam eq info ctor =
  do -- Simultaneously compute the LHS and its type using the Sigma trick
     -- Begin by making non-param names unique (so we can use them for holes as well)
    (cn1, ctorArgs1, resTy1) <- processCtorArgs info ctor
    (cn2, ctorArgs2, resTy2) <- processCtorArgs info ctor
    elabPatternClause
      (do -- First give consistent bindings to the parameters
          traverse {b=()} (\(n, ty) => do claim n ty ; unfocus n) (getParams info)
          -- Next create holes for arguments - do indices, then a hole for each actual arg
          -- Now make holes for non-param args
          traverse mkArgHole ctorArgs1
          traverse mkArgHole ctorArgs2
          -- Now make holes for the arguments themselves
          arg1 <- newHole "arg1" resTy1
          arg2 <- newHole "arg2" resTy2
          -- Now apply ==, with holes for its args that we will fill with these ones. Most will be solved through unification, but not all.
          holes' <- apply (mkApp (Var eq) (map (Var . fst) (getParams info)))
                          (replicate (length (getParams info) + 2 +
                                      2 * length (getIndices info))
                                     (True, 0))
          solve
          -- We can find the argument positions by counting
          -- holes. Drop the constraints and indices, then take
          -- an arg, then drop the indices again, then take an
          -- arg
          focus (snd !(unsafeNth (length (getParams info) + (length (getIndices info))) holes'))
          apply (Var arg1) []; solve
          focus (snd !(unsafeNth (1 + length (getParams info) + 2 * (length (getIndices info))) holes'))
          apply (Var arg2) []; solve

          -- Now we get the actual arguments in place
          focus arg1
          apply (mkApp (Var cn1) (map (Var . argName . ctorFunArg) ctorArgs1)) []
          solve
          focus arg2
          apply (mkApp (Var cn2) (map (Var . argName . ctorFunArg) ctorArgs2)) []
          solve)
      (checkEq (zip ctorArgs1 ctorArgs2))


  where mkArgHole : CtorArg -> Elab ()
        mkArgHole (CtorParameter _) = return ()
        mkArgHole (CtorField arg) = do claim (argName arg) (argTy arg)
                                       unfocus (argName arg)

        ctorFunArg : CtorArg -> FunArg
        ctorFunArg (CtorParameter a) = a
        ctorFunArg (CtorField a) = a

        checkEq : List (CtorArg, CtorArg) -> Elab ()
        checkEq [] = do fill `(True) ; solve
        checkEq ((CtorParameter _, CtorParameter _)::args) = checkEq args
        checkEq ((CtorField a1, CtorField a2)::args) =
          case erasure a1 of
            Erased => checkEq args
            NotErased =>
              if isRType (argTy a1) then checkEq args
                else
                         do [here, todo] <- apply (Var `{(&&)})
                                                  [(False, 0), (False, 0)]
                            solve
                            focus (snd here)
                            checkArg

                            focus (snd todo)
                            [(_, next)] <- apply `(Delay {t=LazyEval} {a=Bool}) [(False, 0)]
                            solve
                            focus next
                            checkEq args
          where
                checkArg : Elab ()
                checkArg = if headVar (argTy a1) == Just fam
                             then do hs <- apply (mkApp (Var eq) (map (Var . fst) (getParams info)))
                                                 (replicate (length (getParams info) + 2 + 2 * (length (getIndices info)))
                                                            (True, 0))
                                     solve
                                     -- take care of TC dicts
                                     traverse_
                                         (\h => do focus (snd h); resolveTC eq)
                                         (List.take (length (getParams info)) hs)
                                     field1 <- snd <$> unsafeNth (length (getParams info) + length (getIndices info)) hs
                                     field2 <- snd <$> unsafeNth (1 + length (getParams info) + 2 * length (getIndices info)) hs
                                     focus field1; apply (Var (argName a1)) []; solve
                                     focus field2; apply (Var (argName a2)) []; solve


                             else do [ty, inst, x, y] <-
                                       apply (Var (NS (UN "==") ["Classes", "Prelude"])) (replicate 4 (False, 0))
                                     solve
                                     focus (snd x); apply (Var (argName a1)) []; solve
                                     focus (snd y); apply (Var (argName a2)) []; solve
                                     focus (snd ty); apply (argTy a1) []; solve
                                     -- Choose an Eq instance to compare this arg
                                     focus (snd inst)
                                     resolveTC eq
        checkEq _ = empty


catchall : (eq : TTName) -> (info : TyConInfo) -> Elab FunClause
catchall eq info =
   elabPatternClause
     (do apply (Var eq) (replicate (2 * length (args info) + 2) (False, 0))
         solve)
     (do fill `(False)
         solve)

||| Generate the single pattern-match clause for the underlying
||| dictionary object. This clause will take all the arguments to the
||| type constructor as implicit arguments, and it will have access to
||| Eq on each parameter type as a constraint. The right-hand side
||| then returns a dictionary.
|||
||| @ eq the name of the underlying == implementation
||| @ instn the name to be used for the dictionary object
||| @ info a description of the type constructors
||| @ instArgs the arguments 
instClause : (eq, instn : TTName) ->
             (info : TyConInfo) ->
             (instArgs, instConstrs : List FunArg) ->
             Elab (List FunClause)
instClause eq instn info instArgs instConstrs =
  do let baseCtorN = SN (InstanceCtorN `{Classes.Eq})
     (ctorN, _, _) <- lookupTyExact baseCtorN
     clause <- elabPatternClause
                 (do apply (Var instn)
                           (replicate (length instArgs +
                                       length instConstrs)
                                      (True, 0))
                     solve)
                 (do [(_, a), (_, b), (_, c)] <- apply (Var ctorN) [(True, 0), (False, 0), (False, 0)]
                     solve
                     focus b; callEq (return ())
                     focus c
                     callEq $ do [(_, notArg)] <- apply `(not) [(True, 0)]
                                 solve
                                 focus notArg
                     -- the only holes left are the constraint dicts
                     traverse_ (\h => focus h *> resolveTC instn) !getHoles)
     return [clause]

   where

     ||| Fill the holes in the instance constructor with appropriately
     ||| abstracted calls to the underlying implementation. Before
     ||| calling, a script is run to prepare the hole underneath the
     ||| lambdas (e.g. by wrapping it in `not`)
     callEq : Elab () -> Elab ()
     callEq transform =
       do x <- gensym "methArg"
          y <- gensym "methArg"
          attack; intro (Just x)
          attack; intro (Just y)
          transform
          argHs <- apply (Var eq)
                     (replicate (2 * length (getParams info) +
                                 2 * length (getIndices info) +
                                 2) (True, 0))
          focus (snd !(unsafeNth (2 * length (getParams info) +
                                  length (getIndices info))
                                 argHs))
          apply (Var x) []; solve
          focus (snd !(unsafeNth (2 * length (getParams info) +
                                  2 * length (getIndices info) + 1)
                                 argHs))
          apply (Var y) []; solve
          solve; solve -- attacks
          solve -- the hole


abstract
deriveEq : (fam : TTName) -> Elab ()
deriveEq fam =
  do eq <- flip NS !currentNamespace . SN . MetaN fam <$> gensym "equalsImpl"
     datatype <- lookupDatatypeExact fam
     info <- getTyConInfo (tyConArgs datatype) (tyConRes datatype)
     decl <- declareEq fam eq info
     declareType decl
     let instn = NS (SN $ InstanceN `{Classes.Eq} [show fam]) !currentNamespace
     instConstrs <- Foldable.concat <$>
                    traverse (\ param =>
                                case param of
                                  (n, RType) => do constrn <- gensym "instarg"
                                                   return [MkFunArg constrn
                                                                    `(Eq ~(Var n) : Type)
                                                                    Constraint
                                                                    NotErased]
                                  _ => return [])
                             (getParams info)
     let instArgs = map tcFunArg (args info)
     let instRes = RApp (Var `{Classes.Eq})
                        (mkApp (Var fam)
                               (map (Var . tcArgName) (args info)))
     declareType $ Declare instn (instArgs ++ instConstrs) instRes

     clauses <- traverse (ctorClause fam eq info) (constructors datatype)
     defineFunction $ DefineFun eq (clauses ++ [!(catchall eq info)])
     defineFunction $
       DefineFun instn !(instClause eq instn info instArgs instConstrs)
     addInstance `{Classes.Eq} instn
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

decl syntax derive Eq for {n} = %runElab (deriveEq `{n})

derive Eq for MyNat
derive Eq for MyList
derive Eq for MyVect
derive Eq for CompileTimeNat




myNatEqRefl : (n : MyNat) -> n == n = True
myNatEqRefl MyZ = Refl
myNatEqRefl (MyS n') with (myNatEqRefl n')
  myNatEqRefl (MyS n') | ih = rewrite ih in Refl

myNatListEqRefl : (xs : MyList MyNat) -> xs == xs = True
myNatListEqRefl [] = Refl
myNatListEqRefl (x :: xs) with (myNatEqRefl x)
  myNatListEqRefl (x :: xs) | headEq with (myNatListEqRefl xs)
    myNatListEqRefl (x :: xs) | headEq | tailEq = rewrite headEq in
                                                  rewrite tailEq in
                                                  Refl

ctnEqTrivial : (j, k : CompileTimeNat) -> j == k = True
ctnEqTrivial (MkCTN _) (MkCTN _) = Refl
