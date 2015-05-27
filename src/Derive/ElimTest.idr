module ElimTest

import Data.Vect
import Data.So

import Language.Reflection.Elab
import Derive.Elim
import Derive.Kit

||| A strict less-than relation on `Nat`.
|||
||| @ n the smaller number
||| @ m the larger number
data LT' : (n,m : Nat) -> Type where
  ||| n < 1 + n
  LTSucc : LT' n (S n)
  ||| n < m implies that n < m + 1
  LTStep : LT' n m -> LT' n (S m)

mkName : String -> TTName
mkName n = NS (UN n) ["ElimTest"]

data Damn : (qzx : Type) -> qzx -> Type where
  Argh : Damn Nat 3

forEffect : ()
forEffect = %runElab (do deriveElim `{Vect} (mkName "vectElim")
                         deriveElim `{So} (mkName "soElim")
                         deriveElim `{Void} (mkName "voidElim")
                         deriveElim `{LTE} (mkName "lteElim")
                         deriveElim `{LT'} (mkName "ltElim")
                         deriveElim `{Damn} (mkName "damnElim")
                         trivial)
