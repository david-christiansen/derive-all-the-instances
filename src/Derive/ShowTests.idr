module Derive.ShowTests

import Pruviloj
import Derive.Show

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
