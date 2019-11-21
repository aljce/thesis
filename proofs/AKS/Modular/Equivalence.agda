open import Level using (_⊔_)
open import Function using (_$_)
open import Algebra using (CommutativeRing)

module AKS.Modular.Equivalence {c ℓ} (R : CommutativeRing c ℓ) where

open CommutativeRing R using (0#; 1#; _+_; _*_; -_; _-_)
  renaming (Carrier to C)
open CommutativeRing R using (+-cong; +-congˡ; +-congʳ; +-identityʳ; +-assoc; +-comm)
open CommutativeRing R using (-‿inverseʳ; -‿inverseˡ; -‿cong)
open CommutativeRing R using (zeroˡ; distribʳ; distribˡ; *-congˡ; *-assoc; *-comm)
open CommutativeRing R using (_≈_; isEquivalence; setoid; ring)
  renaming (refl to ≈-refl; sym to ≈-sym)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Properties.Ring ring using (-‿distribˡ-*; -‿+-comm; -‿involutive; -0#≈0#)

infix 4 _≈_[mod_]
record _≈_[mod_] (x : C) (y : C) (n : C) : Set (c ⊔ ℓ) where
  constructor modulo
  field
    k : C
    x-y≈k*n : x - y ≈ k * n

refl : ∀ {x} {y} {n} → x ≈ y → x ≈ y [mod n ]
refl {x} {y} {n} x≈y = modulo 0# $ begin
  x - y  ≈⟨ +-congˡ (-‿cong (≈-sym x≈y)) ⟩
  x - x  ≈⟨ -‿inverseʳ x ⟩
  0#     ≈⟨ ≈-sym (zeroˡ n) ⟩
  0# * n ∎

sym : ∀ {x y} {n} → x ≈ y [mod n ] → y ≈ x [mod n ]
sym {x} {y} {n} (modulo k x-y≈k*n) = modulo (- k) $ begin
  y - x       ≈⟨ +-congʳ (≈-sym (-‿involutive y)) ⟩
  - (- y) - x ≈⟨ -‿+-comm (- y) x ⟩
  - (- y + x) ≈⟨ -‿cong (+-comm (- y) x) ⟩
  - (x - y)   ≈⟨ -‿cong x-y≈k*n ⟩
  - (k * n)   ≈⟨ -‿distribˡ-* k n ⟩
  - k * n     ∎

trans : ∀ {x y z} {n} → x ≈ y [mod n ] → y ≈ z [mod n ] → x ≈ z [mod n ]
trans {x} {y} {z} {n} (modulo k₁ x-y≈k₁*n) (modulo k₂ y-z≈k₂*n) = modulo (k₁ + k₂) $ begin
  x - z               ≈⟨ +-congʳ (≈-sym (+-identityʳ x)) ⟩
  x + 0# - z          ≈⟨ +-congʳ (+-congˡ (≈-sym (-‿inverseˡ y))) ⟩
  x + (- y + y) - z   ≈⟨ +-congʳ (≈-sym (+-assoc x (- y) y)) ⟩
  (x - y) + y - z     ≈⟨ +-assoc (x - y) y (- z) ⟩
  (x - y) + (y - z)   ≈⟨ +-cong x-y≈k₁*n y-z≈k₂*n ⟩
  (k₁ * n) + (k₂ * n) ≈⟨ ≈-sym (distribʳ n k₁ k₂) ⟩
  (k₁ + k₂) * n   ∎

+-compat : ∀ {a₁ a₂ b₁ b₂} {n} → a₁ ≈ b₁ [mod n ] → a₂ ≈ b₂ [mod n ] → a₁ + a₂ ≈ b₁ + b₂ [mod n ]
+-compat {a₁} {a₂} {b₁} {b₂} {n} (modulo k₁ a₁-b₁≈k₁*n) (modulo k₂ a₂-b₂≈k₂*n) = modulo (k₁ + k₂) $ begin
  a₁ + a₂ - (b₁ + b₂)     ≈⟨ +-assoc a₁ a₂ (- (b₁ + b₂)) ⟩
  a₁ + (a₂ - (b₁ + b₂))   ≈⟨ +-congˡ (+-congˡ (≈-sym (-‿+-comm b₁ b₂))) ⟩
  a₁ + (a₂ + (- b₁ - b₂)) ≈⟨ +-congˡ (≈-sym (+-assoc a₂ (- b₁) (- b₂))) ⟩
  a₁ + (a₂ - b₁ - b₂)     ≈⟨ +-congˡ (+-congʳ (+-comm a₂ (- b₁))) ⟩
  a₁ + (- b₁ + a₂ - b₂)   ≈⟨ +-congˡ (+-assoc (- b₁) a₂ (- b₂)) ⟩
  a₁ + (- b₁ + (a₂ - b₂)) ≈⟨ ≈-sym (+-assoc a₁ (- b₁) (a₂ - b₂)) ⟩
  (a₁ - b₁) + (a₂ - b₂)   ≈⟨ +-cong a₁-b₁≈k₁*n a₂-b₂≈k₂*n ⟩
  (k₁ * n) + (k₂ * n)     ≈⟨ ≈-sym (distribʳ n k₁ k₂) ⟩
  (k₁ + k₂) * n           ∎

*-compat : ∀ {a₁ a₂ b₁ b₂} {n} → a₁ ≈ b₁ [mod n ] → a₂ ≈ b₂ [mod n ] → a₁ * a₂ ≈ b₁ * b₂ [mod n ]
*-compat {a₁} {a₂} {b₁} {b₂} {n} (modulo k₁ a₁-b₁≈k₁*n) (modulo k₂ a₂-b₂≈k₂*n) = modulo (a₂ * k₁ + b₁ * k₂) $ begin
  a₁ * a₂ - b₁ * b₂                                 ≈⟨ +-congˡ (-‿cong (*-comm b₁ b₂)) ⟩
  a₁ * a₂ - b₂ * b₁                                 ≈⟨ +-congʳ (≈-sym (+-identityʳ (a₁ * a₂))) ⟩
  a₁ * a₂ + 0# - b₂ * b₁                            ≈⟨ +-congʳ (+-congˡ lemma) ⟩
  a₁ * a₂ + (- (b₁ * a₂) + a₂ * b₁) - b₂ * b₁       ≈⟨ +-congʳ (≈-sym (+-assoc (a₁ * a₂) (- (b₁ * a₂)) (a₂ * b₁))) ⟩
  a₁ * a₂ - b₁ * a₂ + a₂ * b₁ - b₂ * b₁             ≈⟨ +-assoc (a₁ * a₂ - b₁ * a₂) (a₂ * b₁) (- (b₂ * b₁)) ⟩
  (a₁ * a₂ - b₁ * a₂) + (a₂ * b₁ - b₂ * b₁)         ≈⟨ +-cong (+-congˡ (-‿distribˡ-* b₁ a₂)) (+-congˡ (-‿distribˡ-* b₂ b₁)) ⟩
  (a₁ * a₂ + (- b₁) * a₂) + (a₂ * b₁ + (- b₂) * b₁) ≈⟨ +-cong (≈-sym (distribʳ a₂ a₁ (- b₁))) (≈-sym (distribʳ b₁ a₂ (- b₂))) ⟩
  (a₁ - b₁) * a₂ + (a₂ - b₂) * b₁                   ≈⟨ +-cong (*-comm (a₁ - b₁) a₂) (*-comm (a₂ - b₂) b₁) ⟩
  a₂ * (a₁ - b₁) + b₁ * (a₂ - b₂)                   ≈⟨ +-cong (*-congˡ a₁-b₁≈k₁*n) (*-congˡ a₂-b₂≈k₂*n) ⟩
  a₂ * (k₁ * n) + b₁ * (k₂ * n)                     ≈⟨ +-cong (≈-sym (*-assoc a₂ k₁ n)) (≈-sym (*-assoc b₁ k₂ n)) ⟩
  a₂ * k₁ * n + b₁ * k₂ * n                         ≈⟨ ≈-sym (distribʳ n (a₂ * k₁) (b₁ * k₂)) ⟩
  (a₂ * k₁ + b₁ * k₂) * n                           ∎
  where
  lemma : 0# ≈ - (b₁ * a₂) + a₂ * b₁
  lemma = begin
    0# ≈⟨ ≈-sym (-‿inverseˡ (b₁ * a₂)) ⟩
    - (b₁ * a₂) + b₁ * a₂ ≈⟨ +-congˡ (*-comm b₁ a₂) ⟩
    - (b₁ * a₂) + a₂ * b₁ ∎

n*x≈0 : ∀ {x} {n} → n * x ≈ 0# [mod n ]
n*x≈0 {x} {n} = modulo x $ begin
  n * x - 0# ≈⟨ +-congˡ -0#≈0# ⟩
  n * x + 0# ≈⟨ +-identityʳ (n * x) ⟩
  n * x      ≈⟨ *-comm n x ⟩
  x * n      ∎
