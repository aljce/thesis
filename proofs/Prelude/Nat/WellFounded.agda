open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Data.Nat.Properties using (+-identityʳ; +-suc; suc-injective)

module Prelude.Nat.WellFounded where

open import Data.Nat.Induction using (Acc; acc) public
open import Prelude.Nat using (ℕ; _+_; _∸_; _≤_; _<_; lte; ∸-mono-<ˡ; ∸-mono-<ʳ)
open ℕ

<-well-founded : ∀ {n} → Acc _<_ n
<-well-founded {n} = wf-hack 1000 n
  where
  wf₁ : ∀ t → Acc _<_ t
  wf₂ : ∀ t b k → suc (b + k) ≡ t → Acc _<_ b

  wf₁ t = acc λ { b (lte k suc[b+k]≡t) → wf₂ t b k suc[b+k]≡t }

  wf₂ (suc t) b zero refl rewrite sym (+-identityʳ b) = wf₁ t
  wf₂ (suc t) b (suc k) suc[b+suc[k]]≡suc[t] rewrite +-suc b k = wf₂ t b k (suc-injective suc[b+suc[k]]≡suc[t])

  -- This hack ignores the proof that b < t for count reduction steps
  -- Acc proofs are erased at compile time but this can help speed up type checking
  wf-hack : ∀ (count t : ℕ) → Acc _<_ t
  wf-hack zero t = wf₁ t
  -- Need to match on n to avoid unfolding on neutral argument!
  wf-hack (suc count) zero = acc (λ b _ → wf-hack count b)
  wf-hack (suc count) (suc _) = acc (λ b _ → wf-hack count b)

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
