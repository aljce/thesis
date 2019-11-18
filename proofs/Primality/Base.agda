open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Nat using (ℕ)

module Primality.Base where

open import Prelude.Nat using (_<_)
open import Prelude.Divisibility using (_∣_)
-- open import Data.Nat.Properties using (*-1-monoid)
-- open import Prelude.Exponentiation *-1-monoid

-- test : 2 ^ 3 ≡ 8
-- test = refl

record IsPrime (p : ℕ) : Set where
  constructor IsPrime✓
  field
    1<p : 1 < p
    ∀i∣p[i≡p] : ∀ {i} → 1 < i → i ∣ p → i ≡ p

record IsComposite (c : ℕ) : Set where
  constructor IsComposite✓
  field
    p : ℕ
    p<c : p < c
    P[c] : IsPrime p
    p∣c : p ∣ c

open import Data.Integer using (ℤ; +_)
-- open import Data.Integer.Literals
open import Data.Integer.Properties using (+-*-commutativeRing)
open import Prelude.Polynomial +-*-commutativeRing

test : ℤ
test = ⟦ ex2 *ᵖ ex2 ⟧ (+ 3)
