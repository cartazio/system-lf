module Telescope where

open import FormalUtils




infixr 5 _::_
-- ⊔ == \lub
data Telescope  (fv : Nat ) (A : Set  ) (F : Nat -> Set  )  : Nat → Set  where
  []  :  Telescope fv A  F  0
  _::_ : ∀ { n : Nat } → Telescope fv A F n -> A × F (fv + n) ->  Telescope fv A F (Nat.suc n)

tcons-inj-head : ∀ {fv : Nat} {A : Set }  {F : Nat -> Set}  {n}  {x y : A ×  F (fv + n)} {xs ys : Telescope fv A  F n}
                   → (xs :: x ) ≡ ( ys :: y ) → ((x ≡ y)  )
tcons-inj-head refl = refl


tcons-inj-tail : ∀  {fv : Nat} {A : Set } {F : Nat -> Set }   {n}
                 {x y : A ×  F (fv + n)}
                   {xs ys : Telescope fv A  F n} →(xs :: x ) ≡ ( ys :: y ) → xs ≡ ys
tcons-inj-tail refl = refl

{-
instance
  EqTel : ∀  { A : Set }  {{EqA : Eq A }} {fv : Nat } {F : Nat -> Set } {{EqF : ∀ {j : Nat} → Eq (F (fv + j)) }} {n}  -> Eq (Telescope fv A F n)
  _==_ {{EqTel}} [] [] = yes refl
  _==_ {{EqTel}} (x :: xs ) (y :: ys )  with x == y
  ... | no neq = no λ eq -> neq (tcons-inj-head eq)
  ... | yes eq  with xs == ys
  ...    | no neq = no λ eqT -> neq (tcons-inj-tail eqT)
  ...    | yes eqT  =  yes ( _::_ $≡ eq *≡ eqT) -- (Telescope._::_ Eq.$≡ eq *≡ eqT)
-}
