module TypeSpec where


open import Data.Fin
open import Function
open import Data.Unit
open import Data.Star as Star
open import Relation.Nullary as Decidable
open import Data.Nat as Nat 
open import Data.Vec
open import Level as ℓ -- \ell
open import Data.Bool as B  --
open import Relation.Binary as RB
open import Relation.Binary.PropositionalEquality 




{-
one approach 
irrlevant == {}
atmost 1 == {≤1}  ==? { ==1, <1 }
exactly1 == { =1 }
atleast 1 == { ≥1  } ==? { ==1, >1}
unrestricted == {=1, ≥1, ≤1} ==? {=1, >1, <1}

issue with this... {} === {<1} right? ie  irrelevant == "<1"

instead of rig on symbols, have rig on sets? (would negation be complementation???)
+ == union 
* == intersection 

lets take this model and name all our "subsets"


-}
data Lin : Set where -- linearity lattice, name not stable :) 
  irr : Lin -- {} or { <1} , think irr == <1 , AKA zero or 0 or ∅
  <=1 : Lin -- {<1, ==1}
  >=1 : Lin -- {>1, ==1}
  --  >1  : Lin -- {<1} -- users should never be able to write this exotic element 
  --   !1  : Lin -- {<1,>1} -- users should never be able to write this exotic element
  one : Lin -- {==1}
  any1 : Lin -- {==1,>1,<1}


data LinPOrd : Lin -> Lin -> Set where 
  irrZero : LinPOrd Lin.irr Lin.one
  unresTop<=1 : LinPOrd Lin.<=1 Lin.any1
  unresTop>=1 : LinPOrd Lin.>=1 Lin.any1
  oneLT<=1 : LinPOrd Lin.one Lin.<=1
  oneLT>=1 : LinPOrd Lin.one Lin.>=1 

eqPred : (x : Lin) -> (y : Lin ) -> Dec (x ≡ y ) 
eqPred one one = yes refl 
eqPred irr irr = yes refl
eqPred >=1 >=1 = yes refl
eqPred <=1 <=1 = yes refl
eqPred any1 any1 = yes refl
eqPred irr <=1 = no (λ ())
eqPred irr >=1 = no (λ ())
eqPred irr one = no (λ ())
eqPred irr any1 = no (λ ())
eqPred <=1 irr = no (λ ())
eqPred <=1 >=1 = no (λ ())
eqPred <=1 one = no (λ ())
eqPred <=1 any1 = no (λ ())
eqPred >=1 irr = no (λ ())
eqPred >=1 <=1 = no (λ ())
eqPred >=1 one = no (λ ())
eqPred >=1 any1 = no (λ ())
eqPred one irr = no (λ ())
eqPred one <=1 = no (λ ())
eqPred one >=1 = no (λ ())
eqPred one any1 = no (λ ())
eqPred any1 irr = no (λ ())
eqPred any1 <=1 = no (λ ())
eqPred any1 >=1 = no (λ ())
eqPred any1 one = no (λ ())

pordPred : Lin -> Lin -> Bool
pordPred irr y = true
pordPred x irr = false
pordPred x any1 = true
pordPred any1 y = false
pordPred <=1 <=1 = true
pordPred <=1 >=1 = false
pordPred <=1 one = false
pordPred >=1 <=1 = false
pordPred >=1 >=1 = true
pordPred >=1 one = false
pordPred one <=1 = true
pordPred one >=1 = true
pordPred one one = true


infixr 6 _::_
-- ⊔ == \lub 
data Telescope {i j} (fv : ℕ ) (A : Set j ) (F : ℕ -> Set i )  : ℕ → Set ( ( i ℓ.⊔ j  )) where
  []  :  Telescope fv A  F  0 
  _::_ : ∀ { n : ℕ } → Telescope fv A F n -> A ->  F (fv Nat.+ n) -> Telescope fv A F (ℕ.suc n)  
{-
forall x , irr <= x 
-}


-- ℕ == \bN 
data τ ( fv : ℕ) : Set where
  var : Fin fv -> τ fv
  Π_Σ_ : ∀  {n m} ->  (Telescope fv  Lin τ n) -> (Telescope (n Nat.+ fv )  Lin τ m) -> τ fv 

-- \vdash == ⊢
-- τ == \ tau
-- data WFτ  
