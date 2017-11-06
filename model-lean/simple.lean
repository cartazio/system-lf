
inductive kinds : Type 
 | Star : kinds 
 | Arr : kinds -> kinds -> kinds 


inductive types   : nat ->  kinds ->  Type 
    | tyvar : forall k  {fv } , fin fv   -> types fv k 
    | tyforall : forall {fv k2} k1  , types (1+fv) k1 -> types (fv) (kinds.Arr k1 k2)

    