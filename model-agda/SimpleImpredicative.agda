{-# OPTIONS --type-in-type #-}
module SimpleImpredicative where


id0 : ∀ {a : Set } ->   a -> a
id0 x = x


-- id1 : {!   !}
-- {b : Set} → b → b) → {b : Set} → b → b
--  YESSS
id1 = id0 {∀ {b : Set} -> b -> b }
