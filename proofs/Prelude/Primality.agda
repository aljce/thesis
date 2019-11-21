open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

module Prelude.Primality where

open import Prelude.Nat using (ℕ; _<_; <-trans; <-irrefl; 0<1+n)
open import Prelude.Divisibility using (_∣_)

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
    p-isPrime : IsPrime p
    p∣c : p ∣ c

record Prime : Set where
  constructor Prime✓
  field
    prime : ℕ
    isPrime : IsPrime prime

prime≢0 : ∀ {p} → IsPrime p → p ≢ 0
prime≢0 (IsPrime✓ 1<p _) p≡0 = <-irrefl (sym p≡0) (<-trans 0<1+n 1<p)
