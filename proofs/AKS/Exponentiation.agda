open import Algebra using (CommutativeMonoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using () renaming (cong to ≡-cong)

module AKS.Exponentiation {c ℓ} (M : CommutativeMonoid c ℓ) where

open import AKS.Nat using (ℕ; _+_; _<_)
open ℕ
open import AKS.Nat using (ℕ⁺; ℕ+; ⟅_⇓⟆)
open import AKS.Nat using (Acc; acc; <-well-founded)
open import AKS.Binary using (2*; 𝔹; 𝔹⁺; ⟦_⇑⟧; ⟦_⇓⟧; ⟦_⇑⟧⁺; ⟦_⇓⟧⁺; ℕ→𝔹→ℕ; ⌈log₂_⌉)
open 𝔹
open 𝔹⁺
open CommutativeMonoid M
  using (_≈_; isEquivalence; setoid; ε; _∙_; ∙-cong; ∙-congˡ; identityˡ; identityʳ; assoc; comm)
  renaming (Carrier to C)
open IsEquivalence isEquivalence using (refl; sym)
open import Relation.Binary.Reasoning.Setoid setoid

_^ⁱ_ : C → ℕ → C
x ^ⁱ zero = ε
x ^ⁱ suc n = x ∙ x ^ⁱ n

^ⁱ-homo : ∀ x n m → x ^ⁱ (n + m) ≈ x ^ⁱ n ∙ x ^ⁱ m
^ⁱ-homo x zero m = sym (identityˡ (x ^ⁱ m))
^ⁱ-homo x (suc n) m = begin
  x ∙ x ^ⁱ (n + m) ≈⟨ ∙-congˡ (^ⁱ-homo x n m) ⟩
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

_^ᵇ⁺_ : C → 𝔹⁺ → C
x ^ᵇ⁺ 𝕓1ᵇ = x
x ^ᵇ⁺ (b 0ᵇ) = (x ∙ x) ^ᵇ⁺ b
x ^ᵇ⁺ (b 1ᵇ) = x ∙ (x ∙ x) ^ᵇ⁺ b

_^ᵇ_ : C → 𝔹 → C
x ^ᵇ 𝕓0ᵇ = ε
x ^ᵇ (+ b) = x ^ᵇ⁺ b

_^⁺_ : C → ℕ⁺ → C
x ^⁺ n = x ^ᵇ⁺ ⟦ n ⇑⟧⁺

_^_ : C → ℕ → C
x ^ n = x ^ᵇ ⟦ n ⇑⟧

x^n≈x^ⁱn : ∀ x n → x ^ n ≈ x ^ⁱ n
x^n≈x^ⁱn x n = begin
  x ^ n ≈⟨ loop x ⟦ n ⇑⟧ ⟩
  x ^ⁱ ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡⟨ ≡-cong (λ t → x ^ⁱ t) (ℕ→𝔹→ℕ n) ⟩
  x ^ⁱ n ∎
  where
  even : ∀ x b → (x ∙ x) ^ᵇ⁺ b ≈ x ^ⁱ 2* ⟦ b ⇓⟧⁺
  loop⁺ : ∀ x b → x ^ᵇ⁺ b ≈ x ^ⁱ ⟦ b ⇓⟧⁺

  even x b = begin
    (x ∙ x) ^ᵇ⁺ b ≈⟨ loop⁺ (x ∙ x) b ⟩
    (x ∙ x) ^ⁱ ⟦ b ⇓⟧⁺ ≈⟨ ∙-^ⁱ-dist x x ⟦ b ⇓⟧⁺ ⟩
    x ^ⁱ ⟦ b ⇓⟧⁺ ∙ x ^ⁱ ⟦ b ⇓⟧⁺ ≈⟨ sym (^ⁱ-homo x ⟦ b ⇓⟧⁺ ⟦ b ⇓⟧⁺) ⟩
    x ^ⁱ 2* ⟦ b ⇓⟧⁺ ∎

  loop⁺ x 𝕓1ᵇ = sym (identityʳ x)
  loop⁺ x (b 0ᵇ) = even x b
  loop⁺ x (b 1ᵇ) = ∙-congˡ (even x b)

  loop : ∀ x b → x ^ᵇ b ≈ x ^ⁱ ⟦ b ⇓⟧
  loop x 𝕓0ᵇ = refl
  loop x (+ b) = loop⁺ x b

^-homo : ∀ x n m → x ^ (n + m) ≈ x ^ n ∙ x ^ m
^-homo x n m = begin
  x ^ (n + m)     ≈⟨ x^n≈x^ⁱn x (n + m) ⟩
  x ^ⁱ (n + m)    ≈⟨ ^ⁱ-homo x n m ⟩
  x ^ⁱ n ∙ x ^ⁱ m ≈⟨ ∙-cong (sym (x^n≈x^ⁱn x n)) (sym (x^n≈x^ⁱn x m)) ⟩
  x ^ n ∙ x ^ m   ∎

x^n≈x^⁺n : ∀ x n → x ^ ⟅ n ⇓⟆ ≈ x ^⁺ n
x^n≈x^⁺n x (ℕ+ n) = refl

^-^⁺-homo : ∀ x n m → x ^ (n + ⟅ m ⇓⟆) ≈ x ^ n ∙ x ^⁺ m
^-^⁺-homo x n (ℕ+ m) = ^-homo x n (suc m)
