open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

module AKS.Nat.Combinatorial where

open import AKS.Nat.Base using (ℕ; _+_; _∸_; _*_; _≤_)
open ℕ
open import AKS.Nat.Properties using (*-identityʳ)
open import AKS.Nat.Properties using (0≤n; ≤-refl; m≤m+n; *-mono-≤; module ≤-Reasoning)
open import AKS.Nat.Properties using (<-irrefl; *-mono-<)
open import AKS.Nat.Divisibility using (_/_)
open ≤-Reasoning

_C_ : ℕ → ℕ → ℕ
n C zero = 1
zero C suc k = 0
suc n C suc k = n C k + n C (suc k)

_! : ℕ → ℕ
zero ! = 1
suc n ! = suc n * n !

1≤n! : ∀ n → 1 ≤ n !
1≤n! zero = ≤-refl
1≤n! (suc n) = begin
  1 ≤⟨ 1≤n! n ⟩
  n ! ≤⟨ m≤m+n ⟩
  n ! + n * n ! ≡⟨ refl ⟩
  (1 + n) ! ∎

n≤n! : ∀ n → n ≤ n !
n≤n! zero = 0≤n
n≤n! (suc n) = begin
  suc n ≡⟨ sym (*-identityʳ (suc n)) ⟩
  suc n * 1 ≤⟨ *-mono-≤ (≤-refl {suc n}) (1≤n! n) ⟩
  (1 + n) ! ∎

_C′_ : ℕ → ℕ → ℕ
n C′ k = (n ! / (k ! * (n ∸ k) !)) {≢⇒¬≟ den≢0}
  where
  den≢0 : k ! * (n ∸ k) ! ≢ 0
  den≢0 den≡0 = <-irrefl (sym den≡0) (*-mono-< (1≤n! k) (1≤n! (n ∸ k)))

nC′0≡1 : ∀ {n} → n C′ 0 ≡ 1
nC′0≡1 {n} = lemma num≡dem
  where
  num≡dem : n ! ≡ (0 ! * (n ∸ 0) !)
  num≡dem = sym (+-identityʳ (n !))
  lemma : ∀ {num dem} .{dem≢0} → num ≡ dem → (num / dem) {dem≢0} ≡ 1
  lemma {num} {_} {dem≢0} refl = n/n≡1 num {dem≢0}

-- 0C′n≡0 : ∀ {k} → 0 C′ k ≡ 0
-- 0C′n≡0 {k} = {!0/n≡0 (k ! * (0 ∸ k) !) {?}!}

-- lem : ∀ {n k} → n C k ≡ n C′ k
-- lem {n} {zero} = sym (nC′0≡1 {n})
-- lem {zero} {suc k} = {!refl!}
-- lem {suc n} {suc k} with lem {n} {k} | lem {n} {suc k}
-- ... | p₁ | p₂ = {!!}

