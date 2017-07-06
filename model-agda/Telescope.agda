module TelescopeList where

open import FormalUtils

infixl 5 _::_

-- ⊔ == \lub
data Telescope  (fv : Nat) (A : Set) (F : Nat -> Set) : Nat → Set  where
  []  :  Telescope fv A  F  0
  _::_ : ∀ { n : Nat } → Telescope fv A F n -> A × F (fv + n) ->  Telescope fv A F (Nat.suc n)

-- open import Telescope using ( [] ; _::_ )

tcons-inj-head : ∀ {fv : Nat} {A : Set }  {F : Nat -> Set}  {n}  {x y : A ×  F (fv + n)} {xs ys : Telescope fv A  F n}
                   → (xs :: x ) ≡ ( ys :: y ) → ((x ≡ y)  )
tcons-inj-head refl = refl


tcons-inj-tail : ∀  {fv : Nat} {A : Set } {F : Nat -> Set }   {n}
                 {x y : A ×  F (fv + n)}
                   {xs ys : Telescope fv A  F n} →(xs :: x ) ≡ ( ys :: y ) → xs ≡ ys
tcons-inj-tail refl = refl


teleMap :  ∀ {F G} {A B} {fv} {s} -> (A -> B) -> (∀ {i} -> F i -> G i)  -> Telescope fv A F s ->  Telescope fv B G s
teleMap a2b f2g [] = []
teleMap a2b f2g (teleA :: (1stA  , 2ndF)) = {!teleMap a2b f2g teleA :: (a2b 1stA , f2g 2ndF)!}

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
