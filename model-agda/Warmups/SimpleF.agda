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

τSubstFancy : ∀  { tfv } -> (barrier : Nat) -> TypeF (1  + barrier  + tfv ) -> TypeF ( barrier + tfv) -> TypeF (barrier + tfv )
τSubstFancy  bar tar t = {!!}

τSubstTypeF_With : {tfv :  Nat } -> TypeF (1 + tfv) -> TypeF tfv -> TypeF tfv
τSubstTypeF tau With arg  = τSubstFancy 0 tau arg

{-
will probably need to add a type context stack to these :)
-}
data TmF (fv : Nat) (tfv : Nat) : TypeF tfv -> Set where
    τ∀Abs : ∀ {τ} ->
      TmF fv  (1 + tfv)  τ  ->
      -------------------------
      TmF fv  tfv   (∀τ τ)

    λAbs : ∀ τdom {τcodom} ->
        -- Church style lambda for now, τdom is explicit
      TmF (1 + fv) (tfv) τcodom ->
      ----------------------------
      TmF fv tfv (τdom →τ τcodom)

    τ∀App : ∀  {τcodom} ->
      (lam : TmF fv tfv (∀τ τcodom)) -> (τdom : TypeF tfv) ->
      -----------------------------------------------------
      TmF fv tfv (τSubstTypeF τcodom With τdom )
