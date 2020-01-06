open import Relation.Nullary.Decidable using (False)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; module ≡-Reasoning)

open import Data.List using (List)
open List

module AKS.Binary.Base where

open import Polynomial.Simple.AlmostCommutativeRing using (AlmostCommutativeRing)
open import Polynomial.Simple.AlmostCommutativeRing.Instances using (module Nat)
open Nat.Reflection using (∀⟨_⟩)

open import AKS.Nat using (ℕ; _+_; _*_; _≟_; _<_; lte; suc-mono-≤)
open ℕ
open import AKS.Nat using (ℕ⁺; ℕ+)
open import AKS.Nat using (Euclidean; Euclidean✓; _div_)
open import AKS.Nat using (Acc; acc; <-well-founded)

2* : ℕ → ℕ
2* n = n + n

infixl 5 _0ᵇ _1ᵇ
data 𝔹⁺ : Set where
  𝕓1ᵇ : 𝔹⁺
  _0ᵇ _1ᵇ : 𝔹⁺ → 𝔹⁺

infixr 4 +_
data 𝔹 : Set where
  𝕓0ᵇ : 𝔹
  +_ : 𝔹⁺ → 𝔹

⟦_⇓⟧⁺ : 𝔹⁺ → ℕ
⟦ 𝕓1ᵇ  ⇓⟧⁺ = 1
⟦ x 0ᵇ ⇓⟧⁺ = 2* ⟦ x ⇓⟧⁺
⟦ x 1ᵇ ⇓⟧⁺ = 1 + 2* ⟦ x ⇓⟧⁺

⟦_⇓⟧ : 𝔹 → ℕ
⟦ 𝕓0ᵇ ⇓⟧ = 0
⟦ + x ⇓⟧ = ⟦ x ⇓⟧⁺

private
  lemma₁ : ∀ {q} → suc q < suc (q + suc (q + zero))
  lemma₁ {q} = lte q (∀⟨ q ∷ [] ⟩)
  lemma₂ : ∀ {q} → suc q < suc (suc (q + suc (q + zero)))
  lemma₂ {q} = lte (suc q) (∀⟨ q ∷ [] ⟩)

⟦_⇑⟧⁺ : ℕ⁺ → 𝔹⁺
⟦ ℕ+ n ⇑⟧⁺ = ⟦ suc n ⇑ <-well-founded ⟧ʰ
  where
  ⟦_⇑_⟧ʰ : ∀ n → Acc _<_ n → ∀ {≢0 : False (n ≟ 0)} → 𝔹⁺
  ⟦ suc n ⇑ acc downward ⟧ʰ with suc n div 2
  ... | Euclidean✓ (suc q) 0 refl r<m = ⟦ suc q ⇑ downward _ lemma₁ ⟧ʰ 0ᵇ
  ... | Euclidean✓ zero 1 refl r<m = 𝕓1ᵇ
  ... | Euclidean✓ (suc q) 1 refl r<m = ⟦ suc q ⇑ downward _ lemma₂ ⟧ʰ 1ᵇ

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero ⇑⟧ = 𝕓0ᵇ
⟦ suc n ⇑⟧ = + ⟦ ℕ+ n ⇑⟧⁺

open import AKS.Nat.Properties using (+-identityʳ)
open import Relation.Binary.PropositionalEquality using (cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import AKS.Unsafe using (trustMe)

ℕ→𝔹→ℕ : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
ℕ→𝔹→ℕ _ = trustMe

-- ℕ→𝔹→ℕ : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
-- ℕ→𝔹→ℕ zero = refl
-- ℕ→𝔹→ℕ (suc n) = ℕ⁺→𝔹⁺→ℕ (suc n) <-well-founded
--   where
--   ℕ⁺→𝔹⁺→ℕ : ∀ n → Acc _<_ n → ∀ {≢0 : False (n ≟ 0)} → ⟦ ⟦ n ⇑⟧⁺ {≢0} ⇓⟧⁺ ≡ n
--   ℕ⁺→𝔹⁺→ℕ (suc n) (acc downward) with suc n div 2
--   ... | Euclidean✓ (suc q) 0 refl r<m = {!!}
--   ... | Euclidean✓ zero 1 refl r<m = refl
--   ... | Euclidean✓ (suc q) 1 refl r<m = {!refl!}

⌈log₂_⌉⁺ : 𝔹⁺ → ℕ
⌈log₂ 𝕓1ᵇ ⌉⁺ = 1
⌈log₂ (b 0ᵇ) ⌉⁺ = 1 + ⌈log₂ b ⌉⁺
⌈log₂ (b 1ᵇ) ⌉⁺ = 1 + ⌈log₂ b ⌉⁺

⌈log₂_⌉ : 𝔹 → ℕ
⌈log₂ 𝕓0ᵇ ⌉ = 0
⌈log₂ + b ⌉ = ⌈log₂ b ⌉⁺

⌊_/2⌋⁺ : 𝔹⁺ → 𝔹⁺
⌊ 𝕓1ᵇ /2⌋⁺ = 𝕓1ᵇ
⌊ b 0ᵇ /2⌋⁺ = b
⌊ b 1ᵇ /2⌋⁺ = b

⌊_/2⌋ : 𝔹 → 𝔹
⌊ 𝕓0ᵇ /2⌋ = 𝕓0ᵇ
⌊ + b /2⌋ = + ⌊ b /2⌋⁺

-- _+ᵇ_ : 𝔹 → 𝔹 → 𝔹
-- n +ᵇ m = ⟦ ⟦ n ⇓⟧ + ⟦ m ⇓⟧ ⇑⟧

-- -- data Bit : Set where
-- --   0𝑏 : Bit
-- --   1𝑏 : Bit

-- -- _+ᵇ⁺_ : 𝔹⁺ → 𝔹⁺ → 𝔹⁺
-- -- n +ᵇ⁺ m = ⟦ ⟦ n ⇓⟧⁺ ⇑⟧⁺
--   -- where
--   -- loop : Bit → 𝔹⁺ → 𝔹⁺ → 𝔹⁺
--   -- loop carry x y = ?

-- -- unique⁺ : ∀ x y → ⟦ x ⇓⟧⁺ ≡ ⟦ y ⇓⟧⁺ → x ≡ y
-- -- unique⁺ 1ᵇ 1ᵇ p = refl
-- -- unique⁺ 1ᵇ (y 0ᵇ) p = {!!}
-- -- unique⁺ 1ᵇ (y 1ᵇ) p = {!!}
-- -- unique⁺ (x 0ᵇ) 1ᵇ p = {!!}
-- -- unique⁺ (x 0ᵇ) (y 0ᵇ) p = {!!}
-- -- unique⁺ (x 0ᵇ) (y 1ᵇ) p = {!!}
-- -- unique⁺ (x 1ᵇ) y p = {!!}

-- -- unique : ∀ x y → ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧ → x ≡ y
-- -- unique 𝕓0ᵇ 𝕓0ᵇ p = refl
-- -- unique 𝕓0ᵇ (𝕓 y) p = {!!}
-- -- unique (𝕓 x) 𝕓0ᵇ p = {!!}
-- -- unique (𝕓 x) (𝕓 y) p = {!!}

module Test where
  eval-unit₁ : ⟦ + 𝕓1ᵇ 0ᵇ 1ᵇ 0ᵇ ⇓⟧ ≡ 10
  eval-unit₁ = refl

  log-unit₁ : ⌈log₂ ⟦ 15 ⇑⟧ ⌉ ≡ 4
  log-unit₁ = refl
