open import Relation.Nullary using (¬_)

module AKS.Fin where

open import AKS.Nat using (ℕ; _+_; _<_)

record Fin (n : ℕ) : Set where
  constructor Fin✓
  field
    i : ℕ
    i<n : i < n

¬Fin0 : ¬ (Fin 0)
¬Fin0 ()

from< : ∀ {i n} → i < n → Fin n
from< {i} i<n = Fin✓ i i<n
