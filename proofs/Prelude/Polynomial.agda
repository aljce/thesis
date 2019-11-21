open import Algebra using (CommutativeRing)

open import Data.Maybe using (Maybe)
open Maybe
open import Data.List using (List)
open List

module Prelude.Polynomial {c ℓ} (R : CommutativeRing c ℓ) where

-- TODO switch to preorder based max
open import Data.Nat using (_⊔_)
open import Prelude.Nat using (ℕ)
open ℕ

open CommutativeRing R using (0#; 1#; _+_; _*_; -_; _-_; ring)
  renaming (Carrier to C)
open CommutativeRing R using (_≈_; isEquivalence; setoid)
  renaming (refl to ≈-refl; sym to ≈-sym)
open import Relation.Binary.Reasoning.Setoid setoid
open CommutativeRing R using (+-cong; +-congˡ; +-congʳ; +-identityʳ; +-identityˡ; +-assoc; +-comm)
open CommutativeRing R using (-‿inverseʳ; -‿inverseˡ; -‿cong)
open CommutativeRing R using (zeroˡ; zeroʳ; distribʳ; distribˡ; *-congˡ; *-congʳ; *-assoc; *-comm)
open import Algebra.Properties.Ring ring using (-‿distribʳ-*; -‿+-comm; -0#≈0#)

open import Polynomial.Simple.AlmostCommutativeRing using (AlmostCommutativeRing; fromCommutativeRing)
open import Polynomial.Simple.Reflection using (solve; solveOver)

ACR : AlmostCommutativeRing c ℓ
ACR = fromCommutativeRing R (λ _ → nothing)

data Degree : Set where
  -∞ : Degree
  ⟨_⟩ : ℕ → Degree

_max_ : Degree → Degree → Degree
-∞ max d₂ = d₂
d₁ max -∞ = d₁
⟨ d₁ ⟩ max ⟨ d₂ ⟩ = ⟨ d₁ ⊔ d₂ ⟩

1+ : Degree → Degree
1+ -∞ = ⟨ 0 ⟩
1+ ⟨ d ⟩ = ⟨ suc d ⟩

data Polynomial : Set c where
  0ᵖ : Polynomial
  _+x∙_ : C → Polynomial → Polynomial

deg : Polynomial → Degree
deg 0ᵖ = -∞
deg (_ +x∙ p) = 1+ (deg p)

_+ᵖ_ : Polynomial → Polynomial → Polynomial
0ᵖ +ᵖ q = q
p +ᵖ 0ᵖ = p
(k₁ +x∙ p) +ᵖ (k₂ +x∙ q) = (k₁ + k₂) +x∙ (p +ᵖ q)

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; sym to ≡-sym)

lemma : ∀ p q → deg (p +ᵖ q) ≡ deg p max deg q
lemma 0ᵖ q = ≡-refl
lemma p 0ᵖ = {!!}
lemma (k₁ +x∙ p) (k₂ +x∙ q) = {!!}

-- data ℙ : Degree → Set c where
--   𝕡0 : ℙ -∞
--   _+x∙_ : ∀ {d} → C → ℙ d → ℙ (1+ d)

-- open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; sym to ≡-sym)

-- test : ∀ d₁ d₂ → 1+ d₁ max 1+ d₂ ≡ 1+ (d₁ max d₂)
-- test = ?

-- _ℙ+_ : ∀ {d₁ d₂} → ℙ d₁ → ℙ d₂ → ℙ (d₁ max d₂)
-- 𝕡0 ℙ+ q = q
-- (k₁ +x∙ p) ℙ+ 𝕡0 = {!!}
-- _ℙ+_ {d₁} {d₂} (k₁ +x∙ p) (k₂ +x∙ q)  rewrite test d₁ d₂ = {!!} +x∙ ?

-- data Polynomial : Set c where
--   0ᵖ : Polynomial
--   _+x∙_ : C → Polynomial → Polynomial

-- 1ᵖ : Polynomial
-- 1ᵖ = 1# +x∙ 0ᵖ

-- ⟦_⟧ : Polynomial → C → C
-- ⟦ 0ᵖ ⟧ x = 0#
-- ⟦ k +x∙ p ⟧ x = k + x * ⟦ p ⟧ x

-- infixl 6 _+ᵖ_
-- _+ᵖ_ : Polynomial → Polynomial → Polynomial
-- 0ᵖ +ᵖ q = q
-- p +ᵖ 0ᵖ = p
-- (k₁ +x∙ p) +ᵖ (k₂ +x∙ q) = (k₁ + k₂) +x∙ (p +ᵖ q)

-- infixl 7 _∙ᵖ_
-- _∙ᵖ_ : C → Polynomial → Polynomial
-- a ∙ᵖ 0ᵖ = 0ᵖ
-- a ∙ᵖ (k +x∙ p) = (a * k) +x∙ (a ∙ᵖ p)

-- x∙_ : Polynomial → Polynomial
-- x∙ p = 0# +x∙ p

-- 𝑋 : Polynomial
-- 𝑋 = x∙ 1ᵖ

-- infixl 7 _*ᵖ_
-- _*ᵖ_ : Polynomial → Polynomial → Polynomial
-- 0ᵖ *ᵖ q = 0ᵖ
-- p *ᵖ 0ᵖ = 0ᵖ
-- (k₁ +x∙ p) *ᵖ (k₂ +x∙ q) = (k₁ * k₂) +x∙ (k₁ ∙ᵖ q +ᵖ k₂ ∙ᵖ p +ᵖ x∙ (p *ᵖ q))
-- -- (k₁ + x * p[x]) * (k₂ + x * q[x]) = k₁ * k₂ + x * (k₁ * q[x] + k₂ * p[x] + x * (p[x] * q[x]))

-- -ᵖ_ : Polynomial → Polynomial
-- -ᵖ 0ᵖ = 0ᵖ
-- -ᵖ (x +x∙ p) = (- x) +x∙ (-ᵖ p)

-- +ᵖ-homo : ∀ p q x → ⟦ p +ᵖ q ⟧ x ≈ ⟦ p ⟧ x + ⟦ q ⟧ x
-- +ᵖ-homo 0ᵖ q x = ≈-sym (+-identityˡ (⟦ q ⟧ x ))
-- +ᵖ-homo (k₁ +x∙ p) 0ᵖ x = ≈-sym (+-identityʳ (k₁ + x * ⟦ p ⟧ x))
-- +ᵖ-homo (k₁ +x∙ p) (k₂ +x∙ q) x = begin
--   k₁ + k₂ + x * ⟦ p +ᵖ q ⟧ x            ≈⟨ +-congˡ (*-congˡ (+ᵖ-homo p q x)) ⟩
--   k₁ + k₂ + x * (⟦ p ⟧ x + ⟦ q ⟧ x)     ≈⟨ lemma k₁ k₂ x (⟦ p ⟧ x) (⟦ q ⟧ x) ⟩
--   k₁ + x * ⟦ p ⟧ x + (k₂ + x * ⟦ q ⟧ x) ∎
--   where
--   lemma : ∀ a b c d e → a + b + c * (d + e) ≈ a + c * d + (b + c * e)
--   lemma = solve ACR

-- ∙ᵖ-homo : ∀ a p x → ⟦ a ∙ᵖ p ⟧ x ≈ a * ⟦ p ⟧ x
-- ∙ᵖ-homo a 0ᵖ x = ≈-sym (zeroʳ a)
-- ∙ᵖ-homo a (k +x∙ p) x = begin
--   a * k + x * ⟦ a ∙ᵖ p ⟧ x  ≈⟨ +-congˡ (*-congˡ (∙ᵖ-homo a p x)) ⟩
--   a * k + x * (a * ⟦ p ⟧ x) ≈⟨ lemma a k x (⟦ p ⟧ x) ⟩
--   a * (k + x * ⟦ p ⟧ x)     ∎
--   where
--   lemma : ∀ a b c d → a * b + c * (a * d) ≈ a * (b + c * d)
--   lemma = solve ACR

-- x∙-homo : ∀ p x → ⟦ x∙ p ⟧ x ≈ x * ⟦ p ⟧ x
-- x∙-homo p x = +-identityˡ (x * ⟦ p ⟧ x)

-- foil : ∀ a b c d → (a + b) * (c + d) ≈ a * c + a * d + b * c + b * d
-- foil = solve ACR

-- *ᵖ-homo : ∀ p q x → ⟦ p *ᵖ q ⟧ x ≈ ⟦ p ⟧ x * ⟦ q ⟧ x
-- *ᵖ-homo 0ᵖ q x = ≈-sym (zeroˡ (⟦ q ⟧ x))
-- *ᵖ-homo (k₁ +x∙ p) 0ᵖ x = ≈-sym (zeroʳ (k₁ + x * ⟦ p ⟧ x ))
-- *ᵖ-homo (k₁ +x∙ p) (k₂ +x∙ q) x = begin
--   k₁ * k₂ + x * ⟦ k₁ ∙ᵖ q +ᵖ k₂ ∙ᵖ p +ᵖ x∙ (p *ᵖ q) ⟧ x ≈⟨ +-congˡ (*-congˡ (+ᵖ-homo (k₁ ∙ᵖ q +ᵖ k₂ ∙ᵖ p) (x∙ (p *ᵖ q)) x)) ⟩
--   k₁ * k₂ + x * (⟦ k₁ ∙ᵖ q +ᵖ k₂ ∙ᵖ p ⟧ x + ⟦ x∙ (p *ᵖ q) ⟧ x) ≈⟨ +-congˡ (*-congˡ (+-cong (+ᵖ-homo (k₁ ∙ᵖ q) (k₂ ∙ᵖ p) x) (x∙-homo (p *ᵖ q) x))) ⟩
--   k₁ * k₂ + x * (⟦ k₁ ∙ᵖ q ⟧ x + ⟦ k₂ ∙ᵖ p ⟧ x + x * ⟦ p *ᵖ q ⟧ x) ≈⟨ +-congˡ (*-congˡ (+-cong (+-cong (∙ᵖ-homo k₁ q x) (∙ᵖ-homo k₂ p x)) (*-congˡ (*ᵖ-homo p q x)))) ⟩
--   k₁ * k₂ + x * (k₁ * ⟦ q ⟧ x + k₂ * ⟦ p ⟧ x + (x * (⟦ p ⟧ x * ⟦ q ⟧ x))) ≈⟨ full k₁ k₂ x (⟦ p ⟧ x) (⟦ q ⟧ x) ⟩
--   (k₁ + x * ⟦ p ⟧ x) * (k₂ + x * ⟦ q ⟧ x) ∎
--   where
--   lemma₁ : ∀ a b c d e → c * (a * e + b * d) ≈ a * (c * e) + c * d * b
--   lemma₁ a b c d e = begin
--     c * (a * e + b * d) ≈⟨ distribˡ c (a * e) (b * d) ⟩
--     c * (a * e) + c * (b * d) ≈⟨ +-cong (≈-sym (*-assoc c a e)) (*-congˡ (*-comm b d )) ⟩
--     (c * a) * e + c * (d * b) ≈⟨ +-cong (*-congʳ (*-comm c a)) (≈-sym (*-assoc c d b)) ⟩
--     (a * c) * e + c * d * b   ≈⟨ +-congʳ (*-assoc a c e) ⟩
--     a * (c * e) + c * d * b   ∎
--   lemma₂ : ∀ c d e → c * (c * (d * e)) ≈ c * d * (c * e)
--   lemma₂ c d e = begin
--     c * (c * (d * e)) ≈⟨ *-congˡ (≈-sym (*-assoc c d e)) ⟩
--     c * (c * d * e)   ≈⟨ *-congˡ (*-congʳ (*-comm c d)) ⟩
--     c * (d * c * e)   ≈⟨ *-congˡ (*-assoc d c e) ⟩
--     c * (d * (c * e)) ≈⟨ ≈-sym (*-assoc c d (c * e)) ⟩
--     c * d * (c * e)   ∎
--   full : ∀ a b c d e → a * b + c * (a * e + b * d + (c * (d * e))) ≈ (a + c * d) * (b + c * e)
--   full a b c d e = begin
--     a * b + c * (a * e + b * d + (c * (d * e)))                 ≈⟨ +-congˡ (distribˡ c (a * e + b * d) (c * (d * e))) ⟩
--     a * b + (c * (a * e + b * d) + c * (c * (d * e)))           ≈⟨ +-congˡ (+-cong (lemma₁ a b c d e) (lemma₂ c d e)) ⟩
--     a * b + ((a * (c * e) + (c * d) * b) + ((c * d) * (c * e))) ≈⟨ ≈-sym (+-assoc (a * b) (a * (c * e) + (c * d) * b) ((c * d) * (c * e))) ⟩
--     a * b + (a * (c * e) + (c * d) * b) + (c * d) * (c * e)     ≈⟨ +-congʳ (≈-sym (+-assoc (a * b) (a * (c * e)) ((c * d) * b))) ⟩
--     a * b + a * (c * e) + (c * d) * b + (c * d) * (c * e)       ≈⟨ ≈-sym (foil a (c * d) b (c * e)) ⟩
--     (a + c * d) * (b + c * e)                                   ∎

-- -ᵖ‿homo : ∀ p x → ⟦ -ᵖ p ⟧ x ≈ - ⟦ p ⟧ x
-- -ᵖ‿homo 0ᵖ x = ≈-sym -0#≈0#
-- -ᵖ‿homo (k +x∙ p) x = begin
--   - k + x * ⟦ -ᵖ p ⟧ x  ≈⟨ +-congˡ (*-congˡ (-ᵖ‿homo p x)) ⟩
--   - k + x * - ⟦ p ⟧ x   ≈⟨ +-congˡ (≈-sym (-‿distribʳ-* x (⟦ p ⟧ x))) ⟩
--   - k + - (x * ⟦ p ⟧ x) ≈⟨ -‿+-comm k (x * ⟦ p ⟧ x ) ⟩
--   - (k + x * ⟦ p ⟧ x)   ∎

-- -- 1 + x + x^2
-- ex1 : Polynomial
-- ex1 = 1# +x∙ (1# +x∙ (1# +x∙ 0ᵖ))

-- -- 1 + x + x^2
-- ex2 : Polynomial
-- ex2 = 1ᵖ +ᵖ 𝑋 +ᵖ 𝑋 *ᵖ 𝑋
