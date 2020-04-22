open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

module AKS.Nat.WellFounded where

open import Data.Nat.Induction using (Acc; acc) public
open import AKS.Nat.Base using (ℕ; _+_; _∸_; _≤_; _<_; lte)
open ℕ
open import AKS.Nat.Properties using (+-identityʳ; +-suc; ∸-mono-<ˡ; ∸-mono-<ʳ; suc-injective)

data _≤ⁱ_ : ℕ → ℕ → Set where
  ≤-same : ∀ {n} → n ≤ⁱ n
  ≤-step : ∀ {n m} → n ≤ⁱ m → n ≤ⁱ suc m

_<ⁱ_ : ℕ → ℕ → Set
n <ⁱ m = suc n ≤ⁱ m

<⇒<ⁱ : ∀ {n m} → n < m → n <ⁱ m
<⇒<ⁱ {n} {m} (lte zero refl) rewrite +-identityʳ n = ≤-same
<⇒<ⁱ {n} {m} (lte (suc k) refl) = ≤-step (<⇒<ⁱ (lte k (sym (+-suc n k))))

<-well-founded : ∀ {n} → Acc _<_ n
<-well-founded {n} = wf₁ n
  where
  wf₁ : ∀ t → Acc _<_ t
  wf₂ : ∀ t b → b <ⁱ t → Acc _<_ b
  wf₁ t = acc λ b b<t → wf₂ t b (<⇒<ⁱ b<t)
  wf₂ (suc t) b ≤-same = wf₁ t
  wf₂ (suc t) b (≤-step b<ⁱt) = wf₂ t b b<ⁱt

record [_,_] (low : ℕ) (high : ℕ) : Set where
  inductive
  constructor acc
  field
    downward : ∀ {mid} → low ≤ mid → mid < high → [ low , mid ]
    upward : ∀ {mid} → low < mid → mid ≤ high → [ mid , high ]

binary-search : ∀ {n m} → [ n , m ]
binary-search {n} {m} = loop n m <-well-founded
  where
  loop : ∀ low high → Acc _<_ (high ∸ low) → [ low , high ]
  loop low high (acc next) = acc
    (λ {mid} low≤mid mid<high → loop low mid (next (mid ∸ low) (∸-mono-<ˡ low≤mid mid<high)))
    (λ {mid} low<mid mid≤high → loop mid high (next (high ∸ mid) (∸-mono-<ʳ mid≤high low<mid)))
