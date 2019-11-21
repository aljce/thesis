open import Relation.Nullary using (¬_)

module Prelude.Fin where

open import Prelude.Nat using (ℕ; _+_; _<_)

record Fin (n : ℕ) : Set where
  constructor Fin✓
  field
    i : ℕ
    i<n : i < n

¬Fin0 : ¬ (Fin 0)
¬Fin0 ()

from< : ∀ {i n} → i < n → Fin n
from< {i} i<n = Fin✓ i i<n

-- raise : ∀ {m n} → Fin n → Fin (n + m)
-- raise {m} (Fin✓ i i<n) = Fin✓ (i + m) {!+-mono-< i<n ?!}
