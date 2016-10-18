module Derive.DecEq

import Data.Vect

import Language.Reflection.Elab
import Language.Reflection.Utils

import Derive.Kit
import Derive.Disjoint

decEqN : (tyn : TTName) -> TTName
decEqN tyn = SN $ MetaN tyn (UN "decEqImpl")

tyConArgName : TyConArg -> TTName
tyConArgName (Parameter n _) = n
tyConArgName (Index n _) = n

tyConArgTy : TyConArg -> Raw
tyConArgTy (Parameter _ t) = t
tyConArgTy (Index _ t) = t


tyConTy : List TyConArg -> Raw -> Raw
tyConTy [] res = res
tyConTy (Parameter n t :: args) res = RBind n (Pi t `(Type)) $ tyConTy args res
tyConTy (Index     n t :: args) res = RBind n (Pi t `(Type)) $ tyConTy args res

declareDecEq : TTName -> Datatype -> Elab ()
declareDecEq fn (MkDatatype tyn tyconArgs tyconRes cons) =
  do let tconT = tyConTy tyconArgs
     declareType $
       Declare fn
               [Implicit (tyConArgName arg) (tyConArgTy arg) | arg <- tyconArgs]
               `((x, y : ~(mkApp (Var tyn) (map (Var . tyConArgName) tyconArgs))) ->
                 Dec ((=) {A=~tyconRes} {B=~tyconRes} x y))

makeClause : TTName -> ((TTName, Raw), (TTName, Raw)) -> Elab (Maybe FunClause)
makeClause fn ((cn1, ct1), (cn2, ct2)) =
  if cn1 == cn2
    then pure Nothing
    else
      do (args1, res1) <- stealBindings ct1 (const Nothing)
         (args2, res2) <- stealBindings ct2 (const Nothing)
         let rhsGoal = bindPatTys (args1 ++ args2) $ RType --no
         pure Nothing

makeDecEqClauses : TTName -> List ((TTName, Raw), (TTName, Raw)) -> Elab (List FunClause)
makeDecEqClauses fn cases =
  do res <- traverse (makeClause fn) cases
     pure $ justs res
  where justs : List (Maybe a) -> List a
        justs [] = []
        justs (Nothing::xs) = justs xs
        justs (Just x :: xs) = x :: justs xs

deriveDecEq : (tyn : TTName) -> Elab ()
deriveDecEq tyn' =
  do MkDatatype tyn tyconArgs tyconRes cons <- lookupDatatypeExact tyn'
     mkDisjoint tyn
     let fn = (NS (UN "aaaaaa") ["DecEq", "Derive"]) --decEqN tyn
     declareDecEq fn (MkDatatype tyn tyconArgs tyconRes cons)
     defineFunction $ DefineFun fn !(makeDecEqClauses fn [(c1, c2) | c1 <- cons, c2 <- cons])

forEffect : ()
forEffect = %runElab (do deriveDecEq `{Vect}
                         trivial)
