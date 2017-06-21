module Tools.SimpleVar where
-- This module developed with agda 2.5.2
-- you should configure you environment to have both the
-- standard lib available and the agda-prelude by ulf,
-- cause i'm not sure which i'm going to end up using :)

open import Data.Nat


open import Data.Fin


data 1DVar : ℕ  -> Set where
  Var : ∀ {n : ℕ }  -> Fin n -> 1DVar n

data TyContext (Texp : (ℕ -> Set))  (freeTvars : ℕ)  : ℕ -> Set where
  emptyTy :  TyContext Texp freeTvars 0
  consTy : ∀ {m : ℕ } → ( Texp freeTvars) ->  TyContext Texp freeTvars m
          ->  TyContext Texp freeTvars (ℕ.suc m)


{-
i actually want this to be a little bit stronger, but i go stuck

: ∀  {texp : ℕ -> Set} -> (∀ {n} texp n -> texp (ℕ.suc n))
              -> (∀ {m len}  TyContext texp m len -> TyContext texp (ℕ.suc m) len)
  -- but it got confusing 
-}
tyContextWeakening : ∀ {m len} {texp : ℕ -> Set} -> ( texp m -> texp (ℕ.suc m))
              ->   TyContext texp m len -> TyContext texp (ℕ.suc m) len
tyContextWeakening {m} {len} {texp }f emptyTy = emptyTy
tyContextWeakening {m} {len} {texp } f (consTy x ctx) = consTy (f x) (tyContextWeakening f ctx)
