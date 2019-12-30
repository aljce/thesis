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

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import AKS.Nat using (suc; lte; <-cmp)
open import Relation.Binary using (Tri)
open Tri


lemma : ∀ {n} → Fin (suc n) ≢ Fin n
lemma {ℕ.zero} p = {!!}
lemma {suc n} = {!!}

Fin-injective : ∀ {n m} → Fin n ≡ Fin m → n ≡ m
Fin-injective {n} {m} Fin[n]≡Fin[m] with <-cmp n m
... | tri< (lte k₁ refl) _ _ = {!!}
... | tri≈ _ n≡m _ = n≡m
... | tri> _ _ m<n = {!!}
