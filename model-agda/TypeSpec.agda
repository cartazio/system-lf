module TypeSpec where


open import Data.Fin
open import Function
open import Data.Unit
open import Data.Product
open import Data.Nat as Nat 
open import Data.Vec
open import Level as ℓ -- \ell  

infixr 6 _::_
-- ⊔ == \lub 
data Telescope {i j} (fv : ℕ ) (A : Set j ) (F : ℕ -> Set i )  : ℕ → Set ( ℓ.suc ( i ℓ.⊔ j  )) where
  []  :  Telescope fv A  F  0 
  _::_ : ∀ { n : ℕ } → Telescope fv A F n -> A ->  F (fv Nat.+ n)  ->   Telescope fv A F (ℕ.suc n) 


-- ℕ == \bN 
-- data τ ( fv : ℕ) : Set where
--  var : Fin fv -> τ fv
--  Π_Σ_ : 

-- \vdash == ⊢
-- τ == \ tau
-- data WFτ  
