{-# OPTIONS --experimental-irrelevance #-}

module IsSizingBrokenExample where

{-
-- open import Data.Fin
-- open import Function
-- open import Data.Unit
-- open import Data.Star as Star
-- open import Relation.Nullary as Decidable
-- open import Data.Nat as Nat
-- open import Data.Vec
-- open import Level as ℓ -- \ell
-- import Data.Unit as Unit
-- open import Data.Bool as B  --
-- open import Relation.Binary as RB
-- open import Relation.Binary.PropositionalEquality
-}

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




infixr 5 _::_
-- ⊔ == \lub
data Telescope {i j} (fv : Nat )  (A : Set j ) (F : .{ _ : Size } ->  Nat -> Set i )  : ..{sz : Size} →  Nat → Set ( ( i ℓ.⊔ j  )) where
  []  : ∀ .{sz : Size} -> Telescope fv A  F  {sz} 0
  _::_ : ∀ { n : Nat } .{ q s : Size } →  A ×  F { s} (fv + n) -> Telescope fv  A F {q} n -> Telescope fv  A F {↑ (q ⊔ˢ s)}  (Nat.suc n)

tcons-inj-head : ∀ {i j } {fv : Nat} {A : Set j} .{s : Size } .{q : Size< s}  {F : .{ _ :  Size} -> Nat -> Set i}  {n}
                 {x y : A ×  F { q} (fv + n)}
                   {xs ys : Telescope fv  A  F {s} n} → (x :: xs ) ≡ ( y :: ys ) → ((x ≡ y)  )
tcons-inj-head refl = refl


tcons-inj-tail : ∀ {i j } {fv : Nat} {A : Set j} {F : Nat -> Set i}   {n}
                 {x y : A ×  F (fv + n)}
                   {xs ys : Telescope fv A  F n} →(x :: xs ) ≡ ( y :: ys ) → xs ≡ ys
tcons-inj-tail refl = refl


{-
instance
  EqTel : ∀  {a i} { A : Set a}  {{EqA : Eq A }} {fv : Nat } ..{q : Size} {F : .{_ : Size} -> Nat -> Set i} {{EqF : ∀ .{s:Size} {j : Nat} → Eq (F {q} (fv + j)) }} {n}  -> Eq (Telescope fv {q} A F n)
  _==_ {{EqTel}} [] [] = yes refl
  _==_ {{EqTel}} (x :: xs ) (y :: ys )  with x == y
  ... | no neq = no λ eq -> neq (tcons-inj-head eq)
  ... | yes eq  with xs == ys
  ...    | no neq = no λ eqT -> neq (tcons-inj-tail eqT)
  ...    | yes eqT  =  yes ( _::_ $≡ eq *≡ eqT) -- (Telescope._::_ Eq.$≡ eq *≡ eqT)
-}

teleMap : ∀ {a b} {fv s : Nat } .{q : Size } {A : Set a} {B : Set a} {F : Nat -> .{ _ : Size} ->  Set b} {G :  Nat -> .{ _ : Size} -> Set b}
            (f : ∀ .{j : Size } {i : Nat} -> A × F (fv + i) { j}  -> B × G (fv + i )  {  j})
            -> Telescope fv {q} A F   s -> Telescope fv { q} B G s
teleMap f [] = []
teleMap f (x :: xs) = f  x :: teleMap f xs -- f x :: teleMap f xs
