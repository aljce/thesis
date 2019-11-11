open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; module ≡-Reasoning)

open import Data.Nat.Properties using (+-suc)

module Prelude.Nat.Binary where

open import Prelude.Nat using (ℕ; _+_; _*_; _<_; lte; suc-mono-≤; Euclidean; Euclidean✓; _div_)
open ℕ
open import Prelude.Nat.WellFounded using (Acc; acc; <-well-founded)

data 𝔹 : Set where
  𝕫 : 𝔹
  𝕖_ : 𝔹 → 𝔹
  𝕠_ : 𝔹 → 𝔹

2* : ℕ → ℕ
2* n = n + n

⟦_⇓⟧ : 𝔹 → ℕ
⟦ 𝕫 ⇓⟧ = 0
⟦ 𝕖 b ⇓⟧ = 2* ⟦ b ⇓⟧
⟦ 𝕠 b ⇓⟧ = 1 + 2* ⟦ b ⇓⟧

⟦_⇑⟧ : ℕ → 𝔹
⟦ n ⇑⟧ = loop n <-well-founded
  where
  loop : ∀ x → Acc _<_ x → 𝔹
  loop zero _ = 𝕫
  loop (suc x) (acc downward) with suc x div 2
  ... | Euclidean✓ q 1 x≡1+q*2 _ = 𝕠 (loop q (downward q (lte (q + zero) (sym x≡1+q*2))))
  ... | Euclidean✓ (suc q) 0 x≡0+q*2 _ = 𝕖 (loop (suc q) (downward (suc q) (lte (q + zero) (lemma₁ q x≡0+q*2))))
    where
    lemma₁ : ∀ q → suc x ≡ suc q + suc (q + zero) → suc (suc (q + (q + zero))) ≡ suc x
    lemma₁ q refl = cong (λ t → suc t) (sym (+-suc q (q + zero)))

open import Prelude.Unsafe using (TODO)

ℕ→𝔹→ℕ : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
ℕ→𝔹→ℕ n = loop n <-well-founded
  where
  loop : ∀ x → Acc _<_ x → ⟦ ⟦ x ⇑⟧ ⇓⟧ ≡ x
  loop zero a = refl
  loop (suc x) (acc downward) with suc x div 2
  ... | Euclidean✓ q 1 refl _ = TODO
  ... | Euclidean✓ (suc q) 0 refl _ = TODO


test : ℕ → 𝔹
test n = ⟦ n ⇑⟧

⌈log₂_⌉ : ℕ → ℕ
⌈log₂_⌉ zero = zero
⌈log₂_⌉ (suc n) = loop ⟦ n ⇑⟧
  where
  loop : 𝔹 → ℕ
  loop 𝕫 = 0
  loop (𝕖 b) = 1 + loop b
  loop (𝕠 b) = 1 + loop b

-- open import Data.Product
-- open import Relation.Binary.PropositionalEquality using (_≢_)

-- ¬unique : ∃ λ x → ∃ λ y → x ≢ y × ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧
-- ¬unique = 𝕫 , 𝕖 𝕫 , (λ ()) , refl
