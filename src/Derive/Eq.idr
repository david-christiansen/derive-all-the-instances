module Derive.Eq

import Data.Vect

import Language.Reflection.Elab
import Language.Reflection.Utils
import Pruviloj.Internals.TyConInfo
import Pruviloj.Internals
import public Pruviloj.Core

%access private

isRType : Raw -> Bool
isRType RType = True
isRType _ = False


||| Declare the underlying == function
declareEq : (fam, eq : TTName) -> (info : TyConInfo) -> Elab TyDecl
declareEq fam eq info =
    do let paramArgs = map (\(n, t) => MkFunArg n t Implicit NotErased) (getParams info)

       constrs <- traverse
                     (\(n, t) =>
                        do n' <- gensym "constrarg"
                           pure $ MkFunArg n' `(Eq ~(Var n)) Constraint NotErased) $
                     List.filter (isRType . snd) $
                     getParams info
       arg1 <- applyTyCon (args info) (Var fam)
       arg2 <- applyTyCon (args info) (Var fam)
       pure $ Declare eq (paramArgs ++ constrs ++ arg1 ++ arg2) `(Bool)
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



||| Make the matching clause for a single constructor
ctorClause : (fam, eq : TTName) -> (info : TyConInfo) ->
             (c : (TTName, List CtorArg, Raw)) -> Elab (FunClause Raw)
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
                                     True)
          solve
          -- We can find the argument positions by counting
          -- holes. Drop the constraints and indices, then take
          -- an arg, then drop the indices again, then take an
          -- arg
          focus !(unsafeNth (length (getParams info) + (length (getIndices info))) holes')
          apply (Var arg1) []; solve
          focus !(unsafeNth (1 + length (getParams info) + 2 * (length (getIndices info))) holes')
          apply (Var arg2) []; solve

          -- Now we get the actual arguments in place
          focus arg1
          apply (mkApp (Var cn1) (map (Var . name . ctorFunArg) ctorArgs1)) []
          solve
          focus arg2
          apply (mkApp (Var cn2) (map (Var . name . ctorFunArg) ctorArgs2)) []
          solve)
      (checkEq (zip ctorArgs1 ctorArgs2))


  where mkArgHole : CtorArg -> Elab ()
        mkArgHole (CtorParameter _) = pure ()
        mkArgHole (CtorField arg) = do claim (name arg) (type arg)
                                       unfocus (name arg)

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
              if isRType (type a1) then checkEq args
                else
                         do [here, todo] <- apply (Var `{(&&)})
                                                  [False, False]
                            solve
                            focus here
                            checkArg

                            focus todo
                            [next] <- apply `(Delay {t=LazyValue} {a=Bool}) [False]
                            solve
                            focus next
                            checkEq args
          where
                checkArg : Elab ()
                checkArg = if headName (type a1) == Just fam
                             then do args <- Tactics.apply (mkApp (Var eq) (map (Var . fst) (getParams info)))
                                                   (replicate (length (getParams info) + 2 + 2 * (length (getIndices info)))
                                                               True)
                                     solve
                                     -- take care of TC dicts
                                     traverse_
                                         (\h => do focus h; resolveTC eq)
                                         (List.take (length (getParams info)) args)
                                     field1 <- unsafeNth (length (getParams info) + length (getIndices info)) args
                                     field2 <- unsafeNth (1 + length (getParams info) + 2 * length (getIndices info)) args
                                     focus field1; apply (Var (name a1)) []; solve
                                     focus field2; apply (Var (name a2)) []; solve


                             else do [ty, inst, x, y] <-
                                       apply (Var (NS (UN "==") ["Interfaces", "Prelude"])) (replicate 4 False)
                                     solve
                                     focus x; apply (Var (name a1)) []; solve
                                     focus y; apply (Var (name a2)) []; solve
                                     focus ty; apply (type a1) []; solve
                                     -- Choose an Eq instance to compare this arg
                                     focus inst
                                     resolveTC eq
        checkEq _ = empty


catchall : (eq : TTName) -> (info : TyConInfo) -> Elab (FunClause Raw)
catchall eq info =
   elabPatternClause
     (do apply (Var eq) (replicate (2 * length (args info) + 2) False)
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
             Elab (List (FunClause Raw))
instClause eq instn info instArgs instConstrs =
  do let baseCtorN = SN (ImplementationCtorN `{Interfaces.Eq})
     (ctorN, _, _) <- lookupTyExact baseCtorN
     clause <- elabPatternClause
                 (do apply (Var instn)
                           (replicate (length instArgs +
                                       length instConstrs)
                                      True)
                     solve)
                 (do [a, b, c] <- apply (Var ctorN) [True, False, False]
                     solve
                     focus b; callEq (pure ())
                     focus c
                     callEq $ do [notArg] <- apply `(not) [True]
                                 solve
                                 focus notArg
                     -- the only holes left are the constraint dicts
                     traverse_ (\h => focus h *> resolveTC instn) !getHoles)
     pure [clause]

   where

     ||| Fill the holes in the instance constructor with appropriately
     ||| abstracted calls to the underlying implementation. Before
     ||| calling, a script is run to prepare the hole underneath the
     ||| lambdas (e.g. by wrapping it in `not`)
     callEq : Elab () -> Elab ()
     callEq transform =
       do x <- gensym "methArg"
          y <- gensym "methArg"
          attack; intro x
          attack; intro y
          transform
          argHs <- apply (Var eq)
                     (replicate (2 * length (getParams info) +
                                 2 * length (getIndices info) +
                                 2) True)
          focus !(unsafeNth (2 * length (getParams info) +
                                 length (getIndices info))
                            argHs)
          apply (Var x) []; solve
          focus !(unsafeNth (2 * length (getParams info) +
                             2 * length (getIndices info) + 1)
                            argHs)
          apply (Var y) []; solve
          solve; solve -- attacks
          solve -- the hole


export
deriveEq : (fam : TTName) -> Elab ()
deriveEq fam =
  do eq <- flip NS !currentNamespace . SN . MetaN fam <$> gensym "equalsImpl"
     datatype <- lookupDatatypeExact fam
     info <- getTyConInfo (tyConArgs datatype) (tyConRes datatype)
     decl <- declareEq fam eq info
     declareType decl
     let instn = NS (SN $ ImplementationN `{Interfaces.Eq} [show fam])
                    !currentNamespace
     instConstrs <- Foldable.concat <$>
                    traverse (\ param =>
                                case param of
                                  (n, RType) => do constrn <- gensym "instarg"
                                                   pure [MkFunArg constrn
                                                                    `(Eq ~(Var n) : Type)
                                                                    Constraint
                                                                    NotErased]
                                  _ => pure [])
                             (getParams info)
     let instArgs = map tcFunArg (args info)
     let instRes = RApp (Var `{Interfaces.Eq})
                        (mkApp (Var fam)
                               (map (Var . tcArgName) (args info)))
     declareType $ Declare instn (instArgs ++ instConstrs) instRes

     clauses <- traverse (ctorClause fam eq info) (constructors datatype)
     defineFunction $ DefineFun eq (clauses ++ [!(catchall eq info)])
     defineFunction $
       DefineFun instn !(instClause eq instn info instArgs instConstrs)
     addImplementation `{Interfaces.Eq} instn
     pure ()

  where tcArgName : TyConArg -> TTName
        tcArgName (TyConParameter x) = name x
        tcArgName (TyConIndex x) = name x

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
