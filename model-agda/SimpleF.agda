module SimpleF where

{-
our goal here is to do a phoas/hoas
but avoid needing host level impredicativity

Idea: what if we keep track of the max possible quantifier depth in
type application / quantifier instantiation?

-}

open import Prelude



infixr 5 _→τ_

data TypeF (fv : Nat ) : Set where
     vτ : Fin fv -> TypeF fv
     ∀τ  : TypeF (1 + fv) -> TypeF  fv
     _→τ_ : TypeF fv -> TypeF fv -> TypeF fv -- dependent types put a wrench in this ;)
data TmF (fv : Nat) {tfv : Nat} : TypeF tfv -> Set where
    τAbs : ∀ {τ} ->
      TmF fv { 1 + tfv } τ  ->
      -----------------------------------
      TmF fv  { tfv }  (∀τ τ)
