open import Relation.Nullary.Decidable using (False)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; module ≡-Reasoning)

open import Data.Nat.Properties using (+-suc; +-identityʳ)

module Prelude.Nat.Binary where

open import Prelude.Nat using (ℕ; _+_; _*_; _≟_; _<_; lte; suc-mono-≤; Euclidean; Euclidean✓; _div_)
open ℕ
open import Prelude.Nat.WellFounded using (Acc; acc; <-well-founded)

2* : ℕ → ℕ
2* n = n + n

data Parity (n : ℕ) : Set where
  𝕖 : ∀ k → n ≡ 2* k → Parity n
  𝕠 : ∀ k → n ≡ 1 + 2* k → Parity n

parity : ∀ n → Parity n
parity n with n div 2
... | Euclidean✓ q 0 n≡0+2*q _ rewrite +-identityʳ q = 𝕖 q n≡0+2*q
... | Euclidean✓ q 1 n≡1+2*q _ rewrite +-identityʳ q = 𝕠 q n≡1+2*q

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

{-# TERMINATING #-}
⟦_⇑⟧⁺ : ∀ n {≢0 : False (n ≟ 0)} → 𝔹⁺
⟦ suc n ⇑⟧⁺ with parity (suc n)
⟦ .(suc zero) ⇑⟧⁺ | 𝕠 zero refl = 𝕓1ᵇ
⟦ .(suc (suc k + suc k)) ⇑⟧⁺ | 𝕠 (suc k) refl = ⟦ suc k ⇑⟧⁺ 1ᵇ
⟦ .(suc k + suc k) ⇑⟧⁺ | 𝕖 (suc k) refl = ⟦ suc k ⇑⟧⁺ 0ᵇ

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero ⇑⟧ = 𝕓0ᵇ
⟦ suc n ⇑⟧ = + ⟦ suc n ⇑⟧⁺

{-# TERMINATING #-}
ℕ→𝔹→ℕ : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
ℕ→𝔹→ℕ zero = refl
ℕ→𝔹→ℕ (suc n) with parity (suc n)
ℕ→𝔹→ℕ .(suc zero) | 𝕠 zero refl = refl
ℕ→𝔹→ℕ .(suc (suc k + suc k)) | 𝕠 (suc k) refl rewrite ℕ→𝔹→ℕ (suc k) = refl
ℕ→𝔹→ℕ .(suc k + suc k) | 𝕖 (suc k) refl rewrite ℕ→𝔹→ℕ (suc k) = refl

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

data Bit : Set where
  0𝑏 : Bit
  1𝑏 : Bit

-- _+ᵇ⁺_ : 𝔹⁺ → 𝔹⁺ → 𝔹⁺
-- n +ᵇ⁺ m = ⟦ ⟦ n ⇓⟧⁺ ⇑⟧⁺
  -- where
  -- loop : Bit → 𝔹⁺ → 𝔹⁺ → 𝔹⁺
  -- loop carry x y = ?
  
_+ᵇ_ : 𝔹 → 𝔹 → 𝔹
n +ᵇ m = ⟦ ⟦ n ⇓⟧ + ⟦ m ⇓⟧ ⇑⟧

-- unique⁺ : ∀ x y → ⟦ x ⇓⟧⁺ ≡ ⟦ y ⇓⟧⁺ → x ≡ y
-- unique⁺ 1ᵇ 1ᵇ p = refl
-- unique⁺ 1ᵇ (y 0ᵇ) p = {!!}
-- unique⁺ 1ᵇ (y 1ᵇ) p = {!!}
-- unique⁺ (x 0ᵇ) 1ᵇ p = {!!}
-- unique⁺ (x 0ᵇ) (y 0ᵇ) p = {!!}
-- unique⁺ (x 0ᵇ) (y 1ᵇ) p = {!!}
-- unique⁺ (x 1ᵇ) y p = {!!}

-- unique : ∀ x y → ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧ → x ≡ y
-- unique 𝕓0ᵇ 𝕓0ᵇ p = refl
-- unique 𝕓0ᵇ (𝕓 y) p = {!!}
-- unique (𝕓 x) 𝕓0ᵇ p = {!!}
-- unique (𝕓 x) (𝕓 y) p = {!!}

module Test where
  eval-unit₁ : ⟦ + 𝕓1ᵇ 0ᵇ 1ᵇ 0ᵇ ⇓⟧ ≡ 10
  eval-unit₁ = refl

  log-unit₁ : ⌈log₂ ⟦ 15 ⇑⟧ ⌉ ≡ 4
  log-unit₁ = refl
