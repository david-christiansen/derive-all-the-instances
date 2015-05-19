module Derive.Injective

import Language.Reflection.Elab
import Language.Reflection.Utils

import Derive.Kit

%default total
%access public


private
injectiveMaker : Nat -> TTName
injectiveMaker k = UN $ "injectivityLemma" ++ show k

private
injectiveN : Nat -> TTName -> TTName
injectiveN k n = SN $ MetaN (injectiveMaker k) n

zipWith' : (a -> b -> c) -> List a -> List b -> List c
zipWith' f [] _ = []
zipWith' f _ [] = []
zipWith' f (x::xs) (y::ys) = f x y :: zipWith' f xs ys


makeEqualities : (args1, args2 : List (TTName, Binder Raw)) -> Raw
makeEqualities args1 args2 =
  getTy $ zipWith' (\ar1, ar2 =>
                       the Raw `((=) {A=~(getBinderTy (snd ar1))}
                                     {B=~(getBinderTy (snd ar2))}
                                     ~(Var (fst ar1))
                                     ~(Var (fst ar2))))
                   args1 args2
    where getTy : List Raw -> Raw
          getTy [] = `(():Type)
          getTy [x] = x
          getTy [x, y] = mkPairTy x y
          getTy (x::y::zs) = mkPairTy x (getTy (y::zs))


||| Make the type declaration for an injectivity lemma for a constructor specification
partial
mkInjectiveTy : TTName ->
                (mkGoal : (args1, args2 : List (TTName, Binder Raw)) -> Raw) ->
                (TTName, Raw) -> Elab TyDecl
mkInjectiveTy fn mkGoal (cn, cty) =
     -- Steal the bindings TWICE! That gets us two sets of
     -- quantification with unique names, for the initial equation
  do (args1, res1) <- stealBindings cty (const Nothing)
     (args2, res2) <- stealBindings cty (const Nothing)
     hypN <- gensym "hyp"
     let hypTy : Raw = `((=) {A=~res1} {B=~res2}
                        ~(mkApp (Var cn) (map (Var . fst) args1))
                        ~(mkApp (Var cn) (map (Var . fst) args2)))
     let retTy = mkGoal args1 args2
     return $ Declare fn (map (\(n, b) => Implicit n (getBinderTy b)) (args1 ++ args2) ++ [Explicit hypN hypTy]) retTy



partial
mkInjectiveLhs : TTName -> (TTName, Raw) -> Elab Raw
mkInjectiveLhs fn (cn, cty) =
  do (args, res) <- stealBindings cty (const Nothing)
     let hyp : Raw = `(Refl {A=~res} {x=~(mkApp (Var cn) (map (Var . fst) args))})
     return $ bindPats args $ mkApp (Var fn) (map (Var . fst) args ++ map (Var . fst) args ++ [hyp])


partial
mkInjectiveRhs : TTName -> (TTName, Raw) -> Elab Raw
mkInjectiveRhs fn (cn, cty) =
  do (args, res) <- stealBindings cty (const Nothing)
     let goal = bindPatTys args $ makeEqualities args args
     rhs <- runElab goal $ (do repeatUntilFail bindPat; trivial) <|> trivial
     return !(forgetTypes (fst rhs))

partial
mkInjectiveHelper : (TTName, Raw) -> Elab ()
mkInjectiveHelper con =
  do (args, res) <- stealBindings (snd con) (const Nothing)
     let fn = injectiveN (length args) (fst con)
     declareType $ !(mkInjectiveTy fn makeEqualities con)
     defineFunction $ DefineFun fn [MkFunClause !(mkInjectiveLhs fn con)
                                                !(mkInjectiveRhs fn con)]

partial
deriveInjectivity : TTName -> Elab ()
deriveInjectivity tyn' =
  do MkDatatype tyn _ _ cons <- lookupDatatypeExact tyn'
     traverse_ mkInjectiveHelper cons

forEffect : ()
forEffect = %runElab (do deriveInjectivity `{List}
                         deriveInjectivity `{Nat}
                         fill `(():())
                         solve)
