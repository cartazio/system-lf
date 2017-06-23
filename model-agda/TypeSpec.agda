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


data FullPoLin :  Lin -> Lin -> Set  where
  reflLin : ∀ {m} -> FullPoLin m m 
  irrLTOne : FullPoLin irr one
  irrLT>=1 : FullPoLin irr >=1
  irrLT<=1 : FullPoLin irr <=1
  irrLTany1 : FullPoLin irr any1
  oneLT<=1 : FullPoLin one <=1
  oneLT>=1 : FullPoLin one >=1
  oneLTany1 : FullPoLin one any1
  <=1LTany1 : FullPoLin <=1 any1
  >=1LTany1 : FullPoLin >=1 any1

decLinPO : ∀ (x y : Lin ) -> Dec (FullPoLin x y )
decLinPO irr irr = yes reflLin
decLinPO irr <=1 = yes irrLT<=1
decLinPO irr >=1 = yes irrLT>=1
decLinPO irr one = yes irrLTOne
decLinPO irr any1 = yes irrLTany1
decLinPO <=1 irr = no (λ ())
decLinPO <=1 <=1 = yes reflLin
decLinPO <=1 >=1 = no (λ ())
decLinPO <=1 one = no (λ ())
decLinPO <=1 any1 = yes <=1LTany1
decLinPO >=1 irr = no (λ ())
decLinPO >=1 <=1 = no (λ ())
decLinPO >=1 >=1 = yes reflLin
decLinPO >=1 one = no (λ ())
decLinPO >=1 any1 = yes >=1LTany1
decLinPO one irr = no (λ ())
decLinPO one <=1 = yes oneLT<=1
decLinPO one >=1 = yes oneLT>=1
decLinPO one one = yes reflLin
decLinPO one any1 = yes oneLTany1
decLinPO any1 irr = no (λ ())
decLinPO any1 <=1 = no (λ ())
decLinPO any1 >=1 = no (λ ())
decLinPO any1 one = no (λ ())
decLinPO any1 any1 = yes reflLin




infixr 6 _::_
-- ⊔ == \lub 
data Telescope {i j} (fv : ℕ ) (A : Set j ) (F : ℕ -> Set i )  : ℕ → Set ( ( i ℓ.⊔ j  )) where
  []  :  Telescope fv A  F  0 
  _::_ : ∀ { n : ℕ } → Telescope fv A F n -> A ->  F (fv Nat.+ n) -> Telescope fv A F (ℕ.suc n)  
{-
forall x , irr <= x 
-}


-- ℕ == \bN
-- sugared version of τS 
data τS ( fv : ℕ) : Set where
  var : Fin fv -> τS fv
  Π_Σ_ : ∀  {n m} ->  (Telescope fv  Lin τS n) -> (Telescope (n Nat.+ fv )  Lin τS m) -> τS fv -- Π_Σ_ == \Pi_\Sigma_ 
  ⊕ : ∀ {s} -> Vec (τS fv) s -> τS fv -- ⊕ == \oplus 
  ⊗ : ∀ {s} -> Telescope fv Lin τS s -> τS fv -- ⊗ == \otimes 
  choice : ∀ {s} -> Vec (τS fv) s -> τS fv -- & , often called 'with' 
  par : ∀ {s} -> Vec (τS fv) s -> τS fv -- \& == ⅋ is the other name
{-
We should like to SHOW that all of ⊗ ⊕ ⅋ and & are internalized by Π_Σ_ under CBN or CBV or something 
-- definitely dont need built in ⊗ or par/⅋

note:
for f ∈ ⊗,⊕,⅋,&
the following should be "equivalences/definitially true"
1 = ⊗[],
⊤ = &[],
⊥ = ⅋[],
0 = ⊕[] 
"units/true/false"

likewise, for f,h ∈ (⊗,&), (⊕,⅋)
¬ f ( a) ( b) == h  ( ¬ a) (¬ ) 

the classical laws (including double negation elim)
¬ ¬ a = a  -- an involution! often written (_)^{⊥}
-- one way to think about negation is you switch the side of the turnstyle ⊢   
¬ (a ⊗ b)= ¬ a ⅋ ¬ b
¬ (a ⊕ b) = ¬ a & ¬ b 
¬ (a & b) = ¬ a ⊕ ¬ b 
¬ (a ⅋ b) = ¬ a ⊗ ¬ b 
¬ 1 = ⊥ 
¬ 0 = ⊤ 
¬ ⊥ = 1
¬ ⊤ = 0
-}


data τ ( fv : ℕ) : Set where
  var : Fin fv -> τ fv
  Π_Σ_ : ∀  {n m} ->  (Telescope fv  Lin τ n) -> (Telescope (n Nat.+ fv )  Lin τ m) -> τ fv
  ⊕ : ∀ {s} -> Vec (τ fv) s -> τ fv -- ⊕ == \oplus 
  choice : ∀ {s} -> Vec (τ fv) s -> τ fv -- & 
-- need to 

--- core erased usage  types
-- the 4 tuple operators should be definabled with just this :)
-- after linearity / usage erasure 
data τF ( fv : ℕ) : Set where
  var : Fin fv -> τF fv
  Π_Σ_ : ∀  {n m} ->  (Telescope fv  Lin τF n) -> (Telescope (n Nat.+ fv )  Lin τF m) -> τF fv
  -- replace Lin with Unit 

-- 
--- for 



-- \vdash == ⊢
-- τ == \ tau
-- data WFτ  
