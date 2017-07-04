{-# OPTIONS --experimental-irrelevance #-}

module TypeSpec where

open import Data.Fin
open import Function
open import Data.Unit
open import Data.Star as Star
open import Relation.Nullary as Decidable
open import Data.Nat as Nat
open import Data.Vec as Vec
open import Level as ℓ -- \ell
import Data.Unit as Unit
open import Data.Bool as B  --
open import Relation.Binary as RB
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Size

Nat = ℕ

{-
open import Prelude.Nat as Nat
open import Prelude.Fin
open import Prelude.Decidable as Decidable
open import Prelude.Equality as Eq
open import Agda.Primitive as ℓ
open import Prelude.Semiring renaming ( one to semi1)
open import Prelude.Vec
open import Prelude.Unit as Unit
open import Prelude.Product
open import Prelude.Functor
open import Agda.Builtin.Size
-}

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

data Foo : Size -> Set where
  FC : {i : Size } -> Foo i

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

--instance
--  EqLin : Eq Lin
--  _==_ {{EqLin}} = eqPred


-- you can read "FullPoLin a b" as "a ≤ b"
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




infixr 5 _::_
-- ⊔ == \lub
data Telescope  (fv : Nat ) (A : Set  ) (F : Nat -> Set  )  : Nat → Set  where
  []  :  Telescope fv A  F  0
  _::_ : ∀ { n : Nat } →  A × F (fv Nat.+ n) -> Telescope fv A F n -> Telescope fv A F (Nat.suc n)

tcons-inj-head : ∀ {fv : Nat} {A : Set }  {F : Nat -> Set}  {n}
                 {x y : A ×  F (fv Nat.+ n)}
                   {xs ys : Telescope fv A  F n} → (x :: xs ) ≡ ( y :: ys ) → ((x ≡ y)  )
tcons-inj-head refl = refl


tcons-inj-tail : ∀  {fv : Nat} {A : Set } {F : Nat -> Set }   {n}
                 {x y : A ×  F (fv Nat.+ n)}
                   {xs ys : Telescope fv A  F n} →(x :: xs ) ≡ ( y :: ys ) → xs ≡ ys
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



{-
forall x , irr <= x
-}


-- ℕ == \bN
-- sugared version of τS

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
¬ (a ⅋ b) = ¬ a ⊗ ¬ b --- this one leads to (a⅋b) == ¬ (¬ a ⊗ ¬ b), which  is interesting :)
¬ 1 = ⊥
¬ 0 = ⊤
¬ ⊥ = 1
¬ ⊤ = 0

the exponentials are ! and ?
and if included they obey
¬(!a)= ?(¬ a)
¬(?a)= !(¬ a)
-}
{-
for ⊸
 to input : type "\r-o" or "\r" or "\multimap" or "\-o" with Agda input method
and for ×ₖ write \_k for letter or number k
-}

{-
how to thinkabout a ⅋ b :
a⅋b == ¬ ¬ (a ⅋ b )
(via double negation elim)
¬ ¬ (a ⅋ b ) == ¬ (¬ a ⊗ ¬ b)
(via duality of negation )

then if we desugar ¬ a == a ⊸ ∀ x . x
or as ¬ a = ∀ x , a ⊸ x
then we can read
 ¬ (¬ a ⊗ ¬ b) == ∀ x₁ , ((∀ x₂ . a ⊸ x₂) ⊗ (∀ x₃ . a ⊸ x₃ ) ⊸ x₁

I then claim that
A⅋B ⇒ (or perhaps ≥ or even ≡ !! )
    ≡   ∀ x . ∀ y .
          [(A ⊸ x) ⊗  (B ⊸ y)] ⊸ (x ⊗ y)


lets think about it another way

A ⊸ B ≡ ¬ A ⅋ B
-- double negate
      ≡ ¬ ¬ (¬ A ⅋ B)
      ≡ ¬ ( ¬ ¬ A ⊗ ¬ B)
   (misusing ⊥ here perhaps?)
      ?? ==? [ ((A ⊸ ⊥ )⊸ ⊥) ⊗ ( B ⊸ ⊥)   ] ⊸ ⊥

             send an A to the "implication"
             provide the return continuation for the B you get back

         -- lets make it clearer with double negation elim
          == ( A ⊗ (B ⊸ ⊥)) ⊸ ⊥
          -- give an A and provide the rest of the computation
          --/ return continuation
         -- aka "callback"

--------------
¬ ¬ A ⅋ ¬ ¬ B ≡ ¬ A ⊸ ¬ ¬ B ≡ ¬ A ⊸ B
    OR ≡ ¬ B ⊸ ¬ ¬ A ≡ ¬ B ⊸ A
(because A ⅋ B ≡ B ⅋ A )

----------
¬ ¬  (A ⅋ B) ≡ ( A ⊸ ⊥ ⊗ B ⊸ ⊥ ) ⊸ ⊥
two different continuations / contexts, each receiving one of A and B
------------------
(¬ A ⅋ ¬ B ) ≡ ¬ ¬ (¬ A ⅋ ¬ B)
             ≡ ¬ (¬ ¬ A ⊗ ¬ ¬ B )
       (by double negation elim plus duality)
             ≡    ( A ⊗ B) ⊸ ⊥
--- this is just multiple return values / returning a tuple to the
-- continuation
-}

-- forgot linearity annotations on ⊗ ⊕ choice and par

data τS   ( fv : Nat ) : {- Nat -> -}   Set  where
  var : Fin fv -> τS fv -- 0
  Π_Σ_ : ∀  {n m} ->  (Telescope fv  Lin τS n) -> (Telescope (n Nat.+ fv )  Lin τS m) -> τS fv -- Π_Σ_ == \Pi_\Sigma_
  ⊕ : ∀ {s} -> Vec (τS fv) s -> τS fv -- ⊕ == \oplus
  ⊗ : ∀ {s} -> Telescope fv Lin τS s -> τS fv -- ⊗ == \otimes
  choice : ∀ {s} -> Vec (τS fv) s -> τS fv -- & , often called 'with'
  par : ∀ {s} -> Vec (τS fv) s -> τS fv -- \& == ⅋ is the other name

data τ  ( fv : Nat) : {-  Nat -> -}  Set  where
  var : Fin fv -> τ  fv -- 0
  Π_Σ_ : ∀  {n m} ->  Telescope fv  Lin τ  n -> Telescope (n Nat.+ fv )  Lin τ m  -> τ  fv
  ⊕ : ∀ {s}  -> Vec  (τ  fv) s -> τ  fv -- ⊕ == \oplus
  choice : ∀ {s}  -> Vec (τ  fv) s -> τ  fv -- &
-- need to

--- ,′ == ,\' or ,\prime
desugarTypes : ∀ {fv }  -> τS  fv -> τ  fv
desugarTypes ts = {!!}

--- core erased usage  types
-- the 4 tuple operators should be definabled with just this :)
-- after linearity / usage erasure
data τF ( fv : Nat) : Set where
  var : Fin fv -> τF fv
  Π_Σ_ : ∀  {n m} ->  (Telescope fv  Unit.⊤ τF n) -> (Telescope (n Nat.+ fv )  Unit.⊤ τF m) -> τF fv
  -- replace Lin with Unit (\top aka ⊤ )

--
--- for



-- \vdash == ⊢
-- τ == \ tau
-- data WFτ
