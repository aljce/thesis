open import Relation.Nullary using (¬_)
open import Relation.Binary using (Reflexive; Transitive; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.WithK using (≡-erase)
open ≡-Reasoning

open import Data.Nat using (ℕ; _+_; _*_; _∸_; _<ᵇ_)
open ℕ
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; +-suc; suc-injective)
open import Data.Nat.Induction using (Acc; acc)

open import Data.Sum using (_⊎_)
open _⊎_

module Nat where

infix 4 _≤_
record _≤_ (n : ℕ) (m : ℕ) : Set where
  constructor lte
  field
    k : ℕ
    ≤-proof : n + k ≡ m

0≤n : ∀ {n} → 0 ≤ n
0≤n {n} = lte n refl

≤-refl : Reflexive _≤_
≤-refl {x} = lte 0 (≡-erase (+-identityʳ x))

≤-trans : Transitive _≤_
≤-trans {x} {y} {z} (lte k₁ x+k₁≡y) (lte k₂ y+k₂≡z) = lte (k₁ + k₂) (≡-erase ≤-proof)
  where
  ≤-proof : x + (k₁ + k₂) ≡ z
  ≤-proof = begin
    x + (k₁ + k₂) ≡⟨ sym (+-assoc x k₁ k₂) ⟩
    (x + k₁) + k₂ ≡⟨ cong (λ e → e + k₂) x+k₁≡y ⟩
    y + k₂ ≡⟨ y+k₂≡z ⟩
    z ∎

n≤m⇒1+n≤1+m : ∀ {n m} → n ≤ m → 1 + n ≤ 1 + m
n≤m⇒1+n≤1+m (lte k ≤-proof) = lte k (≡-erase (cong suc ≤-proof))

-- _≤?_ : Decidable _≤_
-- n ≤? m with T? (n <ᵇ m)
-- ... | yes tt = ?
-- ... | no ? = ?

infix 4 _<_ _≮_
_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

_≮_ : ℕ → ℕ → Set
n ≮ m = ¬ (n < m)

n<1+n : ∀ {n} → n < 1 + n
n<1+n = ≤-refl

0<1+n : ∀ {n} → 0 < 1 + n
0<1+n {n} = lte n refl

n≮0 : ∀ {n} → n ≮ 0
n≮0 ()

-- ∸-mono-<ˡ : ∀ {a b c} → a < b → a ∸ c < b ∸ c
-- ∸-mono-<ˡ a<b = {!!}

n≤m⇒n<m⊎n≡m : ∀ {n m} → n ≤ m → n < m ⊎ n ≡ m
n≤m⇒n<m⊎n≡m {n} (lte zero ≤-proof) rewrite ≡-erase (+-identityʳ n) = inj₂ ≤-proof
n≤m⇒n<m⊎n≡m {n} (lte (suc k) ≤-proof) rewrite ≡-erase (+-suc n k) = inj₁ (lte k ≤-proof)

_C_ : ℕ → ℕ → ℕ
n C zero = 1
zero C suc k = 0
suc n C suc k = n C k + n C (suc k)

_! : ℕ → ℕ
zero ! = 1
suc n ! = suc n * n !

nC1+n≡0 : ∀ {n m} → n < m → n C m ≡ 0
nC1+n≡0 {zero} n<m = {!!}
nC1+n≡0 {suc n} n<m = {!!}

-- nCn≡1 : ∀ {n} → n C n ≡ 1
-- nCn≡1 {zero} = refl
-- nCn≡1 {suc n} = {!!}

-- <-trans : Transitive _<_
-- <-trans {x} {y} {z} (lte k₁ 1+x+k₁≡y) (lte k₂ 1+y+k₂≡z) = lte (1 + k₁ + k₂) (≡-erase ≤-proof)
--   where
--   ≤-proof : 1 + x + (1 + k₁ + k₂) ≡ z
--   ≤-proof = begin
--     1 + x + (1 + k₁ + k₂) ≡⟨ {!!} ⟩ z ∎

<-well-founded : ∀ {n} → Acc _<_ n
<-well-founded {n} = wf-hack 1000000 n
  where
  wf₁ : ∀ t → Acc _<_ t
  wf₂ : ∀ t b k → suc (b + k) ≡ t → Acc _<_ b

  wf₁ t = acc λ { b (lte k suc[b+k]≡t) → wf₂ t b k suc[b+k]≡t }

  wf₂ (suc t) b zero refl rewrite sym (+-identityʳ b) = wf₁ t
  wf₂ (suc t) b (suc k) suc[b+suc[k]]≡suc[t] rewrite +-suc b k = wf₂ t b k (suc-injective suc[b+suc[k]]≡suc[t])

  -- This hack ignores the proof that b < t for 1000000 reduction steps
  -- Acc proofs are erased at compile time but this can help speed up type checking
  wf-hack : ∀ (count t : ℕ) → Acc _<_ t
  wf-hack zero t = wf₁ t
  wf-hack (suc count) t = acc (λ b _ → wf-hack count b)

-- record [_,_] (low : ℕ) (high : ℕ) : Set where
--   inductive
--   constructor acc
--   field
--     downward : ∀ {mid} → low ≤ mid → mid < high → [ low , mid ]
--     upward : ∀ {mid} → low < mid → mid ≤ high → [ mid , high ]

-- binary-search : ∀ {n m} → [ n , m ]
-- binary-search {n} {m} = loop n m <-well-founded
--   where
--   loop : ∀ low high → Acc _<_ (high ∸ low) → [ low , high ]
--   loop low high (acc next) = acc
--     (λ {mid} low≤mid mid<high → loop low mid (next (mid ∸ low) {!!}))
--     (λ {mid} low<mid mid≤high → loop mid high (next (high ∸ mid) {!!}) )

-- open import Data.Nat using (_*_)
-- open import Data.Nat.DivMod using (result; _divMod_)
-- open import Data.Fin using (0F; 1F)
-- open import Algebra using (Monoid)

-- module Exp {c ℓ} (S : Monoid c ℓ) where
--   open Monoid S using (ε; _∙_) renaming (Carrier to C)

--   _^ⁱ_ : C → ℕ → C
--   x ^ⁱ zero = ε
--   x ^ⁱ suc n = x ∙ x ^ⁱ n

--   lemma₁ : ∀ {a b} → 1 + a ≡ b * 2 → b ≤ a
--   lemma₁ = {!!}

--   lemma₂ : ∀ {a b} → 1 + a ≡ 1 + b * 2 → b ≤ a
--   lemma₂ = {!!}

--   _^_ : C → ℕ → C
--   x ^ n = loop n <-wellFounded ε
--     where
--     loop : (m : ℕ) → Acc _<_ m → C → C
--     loop 0 _ c = c
--     loop (suc m) (acc downward) c with suc m divMod 2
--     ... | result q 0F 1+m≡q*2 = loop q (downward q (n≤m⇒1+n≤1+m (lemma₁ 1+m≡q*2))) (c ∙ c)
--     ... | result q 1F 1+m≡1+q*2 = x ∙ loop q (downward q (n≤m⇒1+n≤1+m (lemma₂ 1+m≡1+q*2))) (c ∙ c)

-- open import Data.Nat.Properties using (*-1-monoid)
-- open Exp *-1-monoid

-- test : 16 ≡ 2 ^ⁱ 4
-- test = refl
