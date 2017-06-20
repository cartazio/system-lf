module Tools.SimpleVar where
-- This module developed with agda 2.5.2
-- you should configure you environment to have both the
-- standard lib available and the agda-prelude by ulf,
-- cause i'm not sure which i'm going to end up using :)
open import Prelude.Nat
open import Prelude.Fin


data 1DVar : Nat  -> Set where
  Var : ∀ {n : Nat}  -> Fin n -> 1DVar n
