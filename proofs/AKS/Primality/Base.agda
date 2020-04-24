open import Relation.Binary.PropositionalEquality using (_≡_)

module AKS.Primality.Base where

open import AKS.Nat using (ℕ; _<_)
open import AKS.Nat.GCD using (_∣_; _∤_)

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

record Composite : Set where
  constructor Composite✓
  field
    composite : ℕ
    isComposite : IsComposite composite

data Compositionality (n : ℕ) : Set where
  Composite✓ : IsComposite n → Compositionality n
  Prime✓ : (∀ {p} → p < n → IsPrime p → p ∤ n) → Compositionality n

data Primality (n : ℕ) : Set where
  Composite✓ : IsComposite n → Primality n
  Prime✓ : IsPrime n → Primality n
