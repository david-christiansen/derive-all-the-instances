module Derive.Injective

import Language.Reflection.Elab
import Language.Reflection.Utils

import Derive.Kit

%default total
%access public

||| Single-argument injective things
class Injective1 (f : a -> b) where
  isInjective1 : f x = f y -> x = y

||| Double-argument injective things
class Injective2 (f : a -> b -> c) where
  isInjective2 : f x x' = f y y' -> (x = y, x' = y')

||| Triple-argument injective things
class Injective3 (f : a -> b -> c -> d) where
  isInjective3 : f x x' x'' = f y y' y'' -> (x = y, x' = y', x'' = y'')

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
                       the Raw `((=) {A=~(getBinderTy (snd ar1))} {B=~(getBinderTy (snd ar2))} ~(Var (fst ar1)) ~(Var (fst ar2))))
                   args1 args2
    where getTy : List Raw -> Raw
          getTy [] = `(():Type)
          getTy [x] = x
          getTy [x, y] = mkPairTy x y
          getTy (x::y::zs) = mkPairTy x (getTy (y::zs))

||| Make the type declaration for an injectivity lemma for a constructor specification
partial
mkInjectiveTy : (TTName, Raw) -> Elab TyDecl
mkInjectiveTy (cn, cty) =
     -- Steal the bindings TWICE! That gets us two sets of
     -- quantification with unique names, for the initial equation
  do (args1, res1) <- stealBindings cty (const Nothing)
     (args2, res2) <- stealBindings cty (const Nothing)
     hypN <- gensym "hyp"
     let hypTy : Raw = `((=) {A=~res1} {B=~res2}
                        ~(mkApp (Var cn) (map (Var . fst) args1))
                        ~(mkApp (Var cn) (map (Var . fst) args2)))
     let retTy = makeEqualities args1 args2
     let fn = injectiveN (length args1) cn
     return $ Declare fn (map (\(n, b) => Implicit n (getBinderTy b)) (args1 ++ args2) ++ [Explicit hypN hypTy]) retTy

forEffect : ()
forEffect = %runElab (do declareType $ !(mkInjectiveTy (`{List.(::)}, `((a : Type) -> (x : a) -> (xs : List a) -> List a)))
                         fill `(():())
                         solve)
