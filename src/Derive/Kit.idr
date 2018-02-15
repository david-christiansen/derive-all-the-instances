module Derive.Kit

import Data.Vect

import Language.Reflection.Elab
import Language.Reflection.Utils
import Pruviloj.Core

%default total

||| Run something for effects, throwing away the return value
ignore : Functor f => f a -> f ()
ignore x = map (const ()) x

||| Do nothing
skip : Applicative f => f ()
skip = pure ()

last : List a -> Elab a
last [] = fail [TextPart "Unexpected empty list"]
last [x] = pure x
last (_::x::xs) = last (x::xs)

getSigmaArgs : Raw -> Elab (Raw, Raw)
getSigmaArgs `(MkDPair {a=~_} {P=~_} ~rhsTy ~lhs) = pure (rhsTy, lhs)
getSigmaArgs arg = fail [TextPart "Not a sigma constructor"]


||| Ensure that all of a collection of holes was properly solved, to
||| sanity-check a use of `apply`
allSolved : List TTName -> Elab ()
allSolved ns = allSolved' ns !getHoles
  where allSolved' : List TTName -> List TTName -> Elab ()
        allSolved' [] hs = pure ()
        allSolved' (n::ns) hs =
          if elem n hs
            then debugMessage [TextPart "Not all holes were solved! Remaining: ",
                       TextPart $ show n,
                       TextPart $ show hs]
            else allSolved' ns hs

zipH : List a -> List b -> Elab (List (a, b))
zipH [] [] = pure []
zipH (x::xs) (y::ys) = ((x, y) ::) <$> zipH xs ys
zipH _ _ = fail [TextPart "length mismatch"]

assoc : Eq a => a -> List (a, b) -> Elab b
assoc x [] = fail [ TextPart "not found" ]
assoc x ((y, z)::ys) = if x == y then pure z else assoc x ys

doTimes : Applicative m => (n : Nat) -> m a -> m (Vect n a)
doTimes Z x = pure []
doTimes (S k) x = [| x :: (doTimes k x) |]

isRType : Raw -> Bool
isRType RType = True
isRType _ = False

unsafeNth : Nat -> List a -> Elab a
unsafeNth _     []        = fail [TextPart "Ran out of list elements"]
unsafeNth Z     (x :: _)  = pure x
unsafeNth (S k) (_ :: xs) = unsafeNth k xs


headVar : Raw -> Maybe TTName
headVar (RApp f _) = headVar f
headVar (Var n) = Just n
headVar x = Nothing


||| Generate holes suitable as arguments to a term of some type
argHoles : Raw -> Elab (List TTName)
argHoles (RBind n (Pi t _) body) = do n' <- nameFrom n
                                      claim n t
                                      unfocus n
                                      (n ::) <$> argHoles body
argHoles _ = pure []

enumerate : List a -> List (Nat, a)
enumerate xs = enumerate' xs 0
  where enumerate' : List a -> Nat -> List (Nat, a)
        enumerate' [] _ = []
        enumerate' (x::xs) n = (n, x) :: enumerate' xs (S n)


namespace Renamers
  ||| Cause a renamer to forget a renaming
  restrict : (TTName -> Maybe TTName) -> TTName -> (TTName -> Maybe TTName)
  restrict f n n' = if n == n' then Nothing else f n'

  ||| Extend a renamer with a new renaming
  extend : (TTName -> Maybe TTName) -> TTName -> TTName -> (TTName -> Maybe TTName)
  extend f n n' n'' = if n'' == n then Just n' else f n''

  rename : TTName -> TTName -> TTName -> Maybe TTName
  rename from to = extend (const Nothing) from to

||| Alpha-convert `Raw` terms
||| @ subst a partial name substitution function
partial
alphaRaw : (subst : TTName -> Maybe TTName) -> Raw -> Raw
alphaRaw subst (Var n) with (subst n)
  alphaRaw subst (Var n) | Nothing = Var n
  alphaRaw subst (Var n) | Just n' = Var n'
alphaRaw subst (RBind n b tm) =
  let subst' = restrict subst n
      b' = map (alphaRaw subst) b
  in RBind n b' (alphaRaw subst' tm)
alphaRaw subst (RApp tm tm') = RApp (alphaRaw subst tm) (alphaRaw subst tm')
alphaRaw subst RType = RType
alphaRaw subst (RUType x) = RUType x
alphaRaw subst (RConstant c) = RConstant c


||| Grab the binders from around a term, alpha-converting to make their names unique
partial
stealBindings : Raw -> (nsubst : TTName -> Maybe TTName) -> Elab (List (TTName, Binder Raw), Raw)
stealBindings (RBind n b tm) nsubst =
  do n' <- nameFrom n
     (bindings, result) <- stealBindings tm (extend nsubst n n')
     pure ((n', map (alphaRaw nsubst) b) :: bindings, result)
stealBindings tm nsubst = pure ([], alphaRaw nsubst tm)

||| Grab the binders from around a term, assuming that they have been previously uniquified
extractBinders : Raw -> (List (TTName, Binder Raw), Raw)
extractBinders (RBind n b tm) = let (bs, res) = extractBinders tm
                                in ((n, b) :: bs, res)
extractBinders tm = ([], tm)

||| Get the type annotation from a binder
getBinderTy : Binder t -> t
getBinderTy (Lam t) = t
getBinderTy (Pi t _) = t
getBinderTy (Let t _) = t
getBinderTy (Hole t) = t
getBinderTy (GHole t) = t
getBinderTy (Guess t _) = t
getBinderTy (PVar t) = t
getBinderTy (PVTy t) = t

mkDecl : TTName -> List (TTName, Erasure, Binder Raw) -> Raw -> TyDecl
mkDecl fn xs tm = Declare fn (map (\(n, e, b) => MkFunArg  n (getBinderTy b) Implicit e) xs) tm

mkPairTy : Raw -> Raw -> Raw
mkPairTy a b = `((~a, ~b) : Type)

rebind : List (TTName, Binder Raw) -> Raw -> Raw
rebind [] tm = tm
rebind ((n, b) :: nbs) tm = RBind n b $ rebind nbs tm

bindPats : List (TTName, Binder Raw) -> Raw -> Raw
bindPats [] res = res
bindPats ((n, b)::bs) res = RBind n (PVar (getBinderTy b)) $ bindPats bs res

bindPatTys : List (TTName, Binder Raw) -> Raw -> Raw
bindPatTys [] res = res
bindPatTys ((n, b)::bs) res = RBind n (PVTy (getBinderTy b)) $ bindPatTys bs res

updateFunArgTy : (Raw -> Raw) -> FunArg -> FunArg
updateFunArgTy f arg = record {type = f (record {type} arg)} arg

tyConArgName : TyConArg -> TTName
tyConArgName (TyConParameter a) = name a
tyConArgName (TyConIndex a) = name a

setTyConArgName : TyConArg -> TTName -> TyConArg
setTyConArgName (TyConParameter a) n = TyConParameter (record {name = n} a)
setTyConArgName (TyConIndex a) n = TyConIndex (record {name = n} a)

updateTyConArgTy : (Raw -> Raw) -> TyConArg -> TyConArg
updateTyConArgTy f (TyConParameter a) = TyConParameter (record {type = f (type a) } a)
updateTyConArgTy f (TyConIndex a) = TyConIndex (record {type = f (type a) } a)

namespace Tactics



  intro1 : Elab TTName
  intro1 = do g <- snd <$> getGoal
              case g of
                Bind n (Pi _ _) _ => do n' <- nameFrom n
                                        intro n'
                                        pure n'
                _ => fail [ TextPart "Can't intro1 because goal"
                          , TermPart g
                          , TextPart "isn't a function type."]

  intros : Elab (List TTName)
  intros = do g <- snd <$> getGoal
              go g
    where go : TT -> Elab (List TTName)
          go (Bind n (Pi _ _) body) = do n' <- nameFrom n
                                         intro n'
                                         (n' ::) <$> go body
          go _ = pure []
