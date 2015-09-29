||| Various tests of automatically-generated eliminators, to show that
||| the compiler doesn't barf and that they can be used for proving
||| things.
module ElimTest

import Data.Vect
import Data.So
import Control.WellFounded
import Data.Nat.DivMod.IteratedSubtraction

import Pruviloj.Core
import Pruviloj.Derive.Eliminators
import Derive.TestDefs

%default total

mkName : String -> TTName
mkName n = NS (UN n) ["ElimTest"]

mutual
  data U : Type where
    UNIT : U
    PI : (t : U) -> (el t -> U) -> U

  el : U -> Type
  el UNIT = ()
  el (PI ty ret) = (x : el ty) -> (el $ ret x)


mutual
  data Even : Nat -> Type where
    EvenZ : Even Z
    EvenS : Odd n -> Even (S n)
  data Odd : Nat -> Type where
    OddN : Even n -> Odd (S n)


forEffect : ()
forEffect = %runElab (do deriveElim `{Vect} (mkName "vectElim")
                         deriveElim `{Bool} (mkName "boolElim")
                         deriveElim `{List} (mkName "listElim")
                         deriveElim `{So} (mkName "soElim")
                         deriveElim `{Void} (mkName "voidElim")
                         deriveElim `{Nat} (mkName "natElim")
                         deriveElim `{LTE} (mkName "lteElim")
                         deriveElim `{LT'} (mkName "ltElim")
                         deriveElim `{(=)} (mkName "wrongEqElim")
                         deriveElim `{U} (mkName "uElim")
                         deriveElim `{W} (mkName "wElim")
                         deriveElim `{Unit} (mkName "unitElim")
                         deriveElim `{Even} (mkName "evenElim")
                         deriveElim `{Odd} (mkName "oddElim")
                         deriveElim `{Accessible} (mkName "accElim")
                         search)


||| Simple function computed using an eliminator
rev : List a -> List a
rev {a} xs = listElim a xs (const $ List a) [] (\y, _, ys => ys ++ [y])

||| Simple proof by induction using a generated eliminator
total
plusIsAssociative : (x,y,z : Nat) -> plus x (plus y z) = plus (plus x y) z
plusIsAssociative = \x,y,z => natElim x (\n => plus n (plus y z) = plus (plus n y) z) Refl (\n, ih => cong ih)


||| The "shape" of the underlying tree for Nat encoded as a W-type
WNatStep : Bool -> Type
WNatStep b = if b then () else Void

||| Nats, as a W-type
WNat : Type
WNat = W Bool WNatStep

||| Zero (it has no predecessors!)
WZ : WNat
WZ = Sup False void

||| Succ (it has a single predecessor, thus ()!)
wS : WNat -> WNat
wS n = Sup True (const n)


||| The induction principle for Nat, here expressed on Nat encoded as W-types.
|||
||| Note that this only works for this particular encoding of the
||| Nat. A separate, equivalent encoding would not work due to W-types
||| being basically useless in intensional type theory. Nevertheless,
||| it demonstrates that the generated eliminators can be used.
indWNat : (P : WNat -> Type) -> P WZ -> ((n : WNat) -> P n -> P (wS n)) -> (n : WNat) -> P n
indWNat P z s n = wElim Bool WNatStep n P
                    (\b => boolElim b
                            (\b' => (f : WNatStep b' -> WNat) ->
                                    ((x : WNatStep b') -> P (f x)) ->
                                    P (Sup b' f))
                            (\f, _ => rewrite voidFunext f void in z)
                            (\f, ih => rewrite unitFunext f in s (f ()) (ih ())))
  where
    ||| Functional extensionality that uses unsafe features to get it
    ||| to actually compute. This is evil and perhaps even inconsistent:
    ||| replace with a postulate for sanity. But it lets addition of WNat go.
    funext : (f, g : a -> b) -> ((x : a) -> f x = g x) -> f = g
    funext {a} {b} f g fun = really_believe_me (Refl {A=a->b} {x=f})
    voidFunext : (f, g : Void -> a) -> f = g
    voidFunext = \f,g => funext f g (\x => voidElim x (const (f x = g x)))
    unitEta : (x : ()) -> x = ()
    unitEta () = Refl
    unitFunext : (f : () -> a) -> f = \x => f ()
    unitFunext = \f => funext f (\x => f ()) (\x => cong (unitEta x))

addWNat : WNat -> WNat -> WNat
addWNat x y = indWNat (const WNat) y (\_, m => wS m) x



||| Recover the induction principle over well-founded relations from the generated one
accInd' : {rel : a -> a -> Type} -> {P : a -> Type} ->
          (step : (x : a) -> ((y : a) -> rel y x -> P y) -> P x) ->
          (z : a) -> Accessible rel z -> P z
accInd' {a} {rel} {P} step z acc =
  accElim a rel z acc (\x, _ => P x) (\y, acc', ih => step y ih)

