||| Deriving for disjointness lemmas. They are stored as instances of
||| `Uninhabited`, to make them easily accessible and eliminate the
||| need for clever names.
module Derive.Disjoint

import Language.Reflection.Elab
import Language.Reflection.Utils

import Derive.Kit

%default total
%access public

private
disjointMaker : TTName
disjointMaker = UN "disjointnessLemma"


||| Compute the meta-name for a constructor disjointness lemma
private
disjointN : TTName -> TTName -> TTName
disjointN n n' = SN $ MetaN n $ SN $ MetaN disjointMaker n'


mkRhs : TTName -> List (TTName, Binder Raw) -> Raw -> Raw
mkRhs fn bs uninh = foldr (\x, rest => RBind (fst x) (Lam (getBinderTy (snd x))) rest)
                          uninh
                          bs

--TODO: make disjointRhs and disjointTy be the same function

partial
disjointTy : TTName -> (Raw -> Raw) -> (TTName, Raw) -> (TTName, Raw) -> Elab TyDecl
disjointTy fn mkRes (cn1, ct1) (cn2, ct2) =
  do (args1, res1) <- stealBindings ct1 (const Nothing)
     (args2, res2) <- stealBindings ct2 (const Nothing)
     let resTy = mkRes `((=) {A=~res1} {B=~res2}
                             ~(mkApp (Var cn1) (map (Var . fst) args1))
                             ~(mkApp (Var cn2) (map (Var . fst) args2)))
     return $ mkDecl fn (args1 ++ args2) resTy

partial
disjointRhs : TTName -> (Raw -> Raw) -> (TTName, Raw) -> (TTName, Raw) -> Elab Raw
disjointRhs fn mkRes (cn1, ct1) (cn2, ct2) =
  do (args1, res1) <- stealBindings ct1 (const Nothing)
     (args2, res2) <- stealBindings ct2 (const Nothing)
     let resTy = mkRes `((=) {A=~res1} {B=~res2}
                             ~(mkApp (Var cn1) (map (Var . fst) args1))
                             ~(mkApp (Var cn2) (map (Var . fst) args2)))
     return $ mkRhs fn (args1 ++ args2) resTy

||| Given a name for the underlying lemma and two constructors,
||| generate the appropriate `Uninhabited` instance for their
||| disjointness.
partial
defDisjoint : (TTName, (TTName, Raw), (TTName, Raw)) -> Elab ()
defDisjoint (fn, c1, c2) = do decl <- disjointTy fn (\ty => `(~ty -> Void)) c1 c2
                              declareType decl
                              defineFunction $ DefineFun fn []
                              let instN = SN $ MetaN (UN "inst") fn
                              declareType !(disjointTy instN (\t => `(Uninhabited ~t)) c1 c2)
                              rhs <- disjointRhs instN (RApp (Var (SN $ InstanceCtorN `{Uninhabited}))) c1 c2
                              defineFunction $ DefineFun instN [MkFunClause (Var instN) rhs]
                              addInstance `{Uninhabited} instN

||| Derive disjointness lemmas for some type
||| @ tyn the type constructor's name
partial
mkDisjoint : (tyn : TTName) -> Elab ()
mkDisjoint tyn' =
  do MkDatatype tyn _ _ cons <- lookupDatatypeExact tyn'
     let candidates = [ (NS (UN $ show $ disjointN (fst c1) (fst c2)) ["Class"], c1, c2)
                      | c1 <- cons, c2 <- cons
                      , fst c1 /= fst c2
                      ]
     traverse_ defDisjoint candidates



-- data Tree = Empty | Branch Tree Tree | Thing Nat

-- forSideEffect : ()
-- forSideEffect = %runElab (mkDisjoint `{Tree} *> fill `(():()) *> solve)
