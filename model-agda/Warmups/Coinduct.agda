open import Prelude
open import Agda.Builtin.Size
open import Agda.Primitive
record Mu  {x} (i : Size) (A : Set x) (f :  Set x -> Set x) : Set x where
  coinductive
  field
    unrec : ∀ {j : Size< i} ->  f (Mu j A f )
