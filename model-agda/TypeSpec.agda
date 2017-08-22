module TypeSpec where

open import FormalUtils
open import Telescope

{-
one approach
irrelevant == {}
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
the following should be "equivalences/definitionally true"
1 = ⊗[],
⊤ = &[],
⊥ = ⅋[],
0 = ⊕[]
"units/true/false"

likewise, for (f , h) ∈ { (⊗,&), (⊕,⅋) }
¬ f a b == h (¬ a) (¬ b)

the classical laws (including double negation elim)
¬ ¬ a = a  -- an involution! often written (_)^{⊥}
-- one way to think about negation is you switch the side of the turnstyle ⊢
¬ (a ⊗ b) = ¬ a ⅋ ¬ b
¬ (a ⊕ b) = ¬ a & ¬ b
¬ (a & b) = ¬ a ⊕ ¬ b
¬ (a ⅋ b) = ¬ a ⊗ ¬ b --- this one leads to (a⅋b) == ¬ (¬ a ⊗ ¬ b), which is interesting :)
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
how to think about a ⅋ b :
a ⅋ b == ¬ ¬ (a ⅋ b)
(via double negation elim)
¬ ¬ (a ⅋ b) == ¬ (¬ a ⊗ ¬ b)
(via duality of negation)

then if we desugar ¬ a == a ⊸ ∀ x . x
or as ¬ a = ∀ x . a ⊸ x
then we can read
 ¬ (¬ a ⊗ ¬ b) == ∀ x₁ . ((∀ x₂ . a ⊸ x₂) ⊗ (∀ x₃ . a ⊸ x₃ ) ⊸ x₁

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

{-
FIX THIS: for non dependent formulation,
need to distinguish between telescope terms that are values with types, vs
types that have kinds,
only types are telescoping in that simpler setting,
can eg just do a type level rev list  of
data Sorts : Set where
  Kind : Sorts
  Type : Sorts
-- this will keep things from feeling out of sorts ;)

-}

-- full linear logic
data τS   ( fv : Nat ) : {- Nat -> -}   Set  where
  var : Fin fv -> τS fv -- 0
  Π_Σ_ : ∀  {n m} ->  (Telescope fv  Lin τS n) -> (Telescope (n + fv )  Lin τS m) -> τS fv -- Π_Σ_ == \Pi_\Sigma_
  ⊕ : ∀ {s} -> Vec (Lin ×  τS fv) s -> τS fv -- ⊕ == \oplus
  ⊗ : ∀ {s} -> Telescope fv Lin τS s -> τS fv -- ⊗ == \otimes
  choice : ∀ {s} -> Vec (Lin  × τS fv) s -> τS fv -- & , often called 'with'
  par : ∀ {s} -> Vec (Lin × τS fv) s -> τS fv -- \& == ⅋ is the other name
  ¬ : ∀ {s} -> Telescope fv Lin τS s -> τS fv

-- minimal linear logic still giving all connectives (via negation or encodings)
data τ  ( fv : Nat) : {-  Nat -> -}  Set  where
  var : Fin fv -> τ  fv -- 0
  Π_Σ_ : ∀  {n m} ->  Telescope fv  Lin τ  n -> Telescope (n + fv )  Lin τ m  -> τ  fv
  ⊕ : ∀ {s}  -> Vec  (Lin ×   τ  fv) s -> τ  fv -- ⊕ == \oplus
               -- these are all wrong
               --- shuld be (Vec (Lin × τ fv) s )
  choice : ∀ {s}  -> Vec (Lin ×  τ  fv) s -> τ  fv -- &
  ¬ : ∀ {s} -> Telescope fv Lin τ s -> τ fv

--- ,′ == ,\' or ,\prime
desugarTypes : ∀ {fv }  -> τS  fv -> τ  fv
{-# TERMINATING #-}
-- this is evil, but whatever, this code is terminating
--- should try to understand whats wrong / work out the sized formulation later
desugarTypes (var x) = var x
desugarTypes (Π x Σ y) = τ.Π_Σ_ ( teleMap (λ z → z) desugarTypes x) (teleMap (λ z → z) desugarTypes y)
desugarTypes (⊕ x) = τ.⊕  (fmap {!!} x )  -- (fmap  (λ (count ,' tee ) → (count , desugarTypes tee ))  x )
desugarTypes (⊗  x) =  τ.¬ ( [] :: ( one , (τ.¬ ( teleMap (λ z → z) desugarTypes x)  ) ) )
-- ISSUE --- do we need to know the contextual linearity or is one correct
--- seems to be correctl for one,zero >=1, <=1, any
                 -- if telemap carries indices as fv + n, would need subst and nat commutivity /
                 -- zero law to get this to type check
--{s} ( [] :: ( one  , τ.¬ {s} (teleMap  (λ x -> x)  desugarTypes x ) ) )
desugarTypes (choice x) = choice (fmap   ( λ  y  ->  fst y  , desugarTypes (snd y)  ) x)
desugarTypes (par x) = {!!}  -- ¬ ( (λ y → (¬ ( [] :: (one , desugarTypes y)) ))  x )
desugarTypes (¬ x) = ¬ (teleMap (λ z → z) desugarTypes x)

--- core erased usage types -- system F with telescopes
-- the 4 tuple operators should be definabled with just this :)
-- after linearity / usage erasure
data τF ( fv : Nat) : Set where
  var : Fin fv -> τF fv
  Π_Σ_ : ∀  {n m} ->  (Telescope fv  ⊤ τF n) -> (Telescope (n + fv )  ⊤ τF m) -> τF fv
  -- replace Lin with Unit (\top aka ⊤ )

eraseTypes : ∀ {fv} -> τ fv -> τF fv
eraseTypes = {!!}


{-
⊕[a_1 ... a_n]== n-ary sum / disjoint union
⊕[] == VOID / Absurd / Bottom


⅋[a_1 ... a_n ]   == cps version of fork io  for n-ary fork
⅋[] == close thread with all resources finalized

cps into direc style we have
⅋[a1 .. an] == ¬ (⊗[¬ a1 ... ¬ an]) == ⊗[a_1 -> ∅ ... a_n → ∅ ]
⅋[] ==  ...

&[a_1 ... a_n] === cps of RHS in case X of RHS
&[] === RHS of case (x : Void) of RHS

case (x : ⊕[ x_i .. ])  of  &[ x_i ]

empty ⅋ and ⊗ pair up to be "close thread cleanly"

empty & and ⊕ pair up to "abort program from the absurd"  (at least our current semantics / thinking)

-}

--
--- for



-- \vdash == ⊢
-- τ == \ tau
-- data WFτ
