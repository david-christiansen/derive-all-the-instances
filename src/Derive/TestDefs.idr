module Derive.TestDefs

data W : (a : Type) -> (a -> Type) -> Type where
  Sup : (x : a) -> (p x -> W a p) -> W a p
