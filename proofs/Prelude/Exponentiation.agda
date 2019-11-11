open import Algebra using (CommutativeMonoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using () renaming (cong to ≡-cong)

module Prelude.Exponentiation {c ℓ} (M : CommutativeMonoid c ℓ) where

open import Prelude.Nat using (ℕ; _+_; _<_)
open ℕ
open import Prelude.Nat.WellFounded using (Acc; acc; <-well-founded)
open import Prelude.Nat.Binary using (2*; 𝔹; ⟦_⇑⟧; ⟦_⇓⟧; ℕ→𝔹→ℕ)
open 𝔹
open CommutativeMonoid M
  using (_≈_; isEquivalence; setoid; ε; _∙_; ∙-congˡ; identityˡ; identityʳ; assoc; comm)
  renaming (Carrier to C)
open IsEquivalence isEquivalence using (refl; sym)
open import Relation.Binary.Reasoning.Setoid setoid

_^ⁱ_ : C → ℕ → C
x ^ⁱ zero = ε
x ^ⁱ suc n = x ∙ x ^ⁱ n

^ⁱ-homomorphism : ∀ x n m → x ^ⁱ (n + m) ≈ x ^ⁱ n ∙ x ^ⁱ m
^ⁱ-homomorphism x zero m = sym (identityˡ (x ^ⁱ m))
^ⁱ-homomorphism x (suc n) m = begin
  x ∙ x ^ⁱ (n + m) ≈⟨ ∙-congˡ (^ⁱ-homomorphism x n m) ⟩
  x ∙ (x ^ⁱ n ∙ x ^ⁱ m) ≈⟨ sym (assoc _ _ _) ⟩
  x ∙ x ^ⁱ n ∙ x ^ⁱ m ∎

∙-^ⁱ-dist : ∀ x y n → (x ∙ y) ^ⁱ n ≈ x ^ⁱ n ∙ y ^ⁱ n
∙-^ⁱ-dist x y zero = sym (identityˡ ε)
∙-^ⁱ-dist x y (suc n) = begin
  x ∙ y ∙ ((x ∙ y) ^ⁱ n) ≈⟨ ∙-congˡ (∙-^ⁱ-dist x y n) ⟩
  x ∙ y ∙ (x ^ⁱ n ∙ y ^ⁱ n) ≈⟨ assoc _ _ _ ⟩
  x ∙ (y ∙ (x ^ⁱ n ∙ y ^ⁱ n)) ≈⟨ ∙-congˡ (comm _ _) ⟩
  x ∙ (x ^ⁱ n ∙ y ^ⁱ n ∙ y) ≈⟨ ∙-congˡ (assoc _ _ _) ⟩
  x ∙ (x ^ⁱ n ∙ (y ^ⁱ n ∙ y)) ≈⟨ ∙-congˡ (∙-congˡ (comm _ _)) ⟩
  x ∙ (x ^ⁱ n ∙ (y ∙ y ^ⁱ n)) ≈⟨ sym (assoc _ _ _) ⟩
  x ∙ (x ^ⁱ n) ∙ (y ∙ (y ^ⁱ n)) ∎

_^ᵇ_ : C → 𝔹 → C
x ^ᵇ 𝕫 = ε
x ^ᵇ (𝕖 b) = (x ∙ x) ^ᵇ b
x ^ᵇ (𝕠 b) = x ∙ (x ∙ x) ^ᵇ b

_^_ : C → ℕ → C
x ^ n = x ^ᵇ ⟦ n ⇑⟧

x^n≈x^ⁱn : ∀ x n → x ^ n ≈ x ^ⁱ n
x^n≈x^ⁱn x n = begin
  x ^ n ≈⟨ loop x ⟦ n ⇑⟧ ⟩
  x ^ⁱ ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡⟨ ≡-cong (λ t → x ^ⁱ t) (ℕ→𝔹→ℕ n) ⟩
  x ^ⁱ n ∎
  where
  even : ∀ x b → (x ∙ x) ^ᵇ b ≈ x ^ⁱ 2* ⟦ b ⇓⟧
  loop : ∀ x b → x ^ᵇ b ≈ x ^ⁱ ⟦ b ⇓⟧

  even x b = begin
    (x ∙ x) ^ᵇ b ≈⟨ loop (x ∙ x) b ⟩
    (x ∙ x) ^ⁱ ⟦ b ⇓⟧ ≈⟨ ∙-^ⁱ-dist x x ⟦ b ⇓⟧  ⟩
    x ^ⁱ ⟦ b ⇓⟧ ∙ x ^ⁱ ⟦ b ⇓⟧ ≈⟨ sym (^ⁱ-homomorphism x ⟦ b ⇓⟧ ⟦ b ⇓⟧) ⟩
    x ^ⁱ 2* ⟦ b ⇓⟧ ∎

  loop x 𝕫 = refl
  loop x (𝕖 b) = even x b
  loop x (𝕠 b) = ∙-congˡ (even x b)
