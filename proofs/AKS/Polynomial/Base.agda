open import Algebra using (RawRing)

module AKS.Polynomial.Base {c ℓ} (R : RawRing c ℓ) where

-- TODO switch to preorder based max
open import Data.Nat using (_⊔_)
open import AKS.Nat using (ℕ)
open ℕ

open RawRing R using (0#; 1#; _+_; _*_; -_)
  renaming (Carrier to C)

_-_ : C → C → C
x - y = x + (- y)

-- data Degree : Set where
--   -∞ : Degree
--   ⟨_⟩ : ℕ → Degree

-- _max_ : Degree → Degree → Degree
-- -∞ max d₂ = d₂
-- d₁ max -∞ = d₁
-- ⟨ d₁ ⟩ max ⟨ d₂ ⟩ = ⟨ d₁ ⊔ d₂ ⟩

-- 1+ : Degree → Degree
-- 1+ -∞ = ⟨ 0 ⟩
-- 1+ ⟨ d ⟩ = ⟨ suc d ⟩

-- deg : Polynomial → Degree
-- deg 0ᵖ = -∞
-- deg (_ +x∙ p) = 1+ (deg p)

data Polynomial : Set c where
  0ᵖ : Polynomial
  _+x∙_ : C → Polynomial → Polynomial

⟦_⟧ : Polynomial → C → C
⟦ 0ᵖ ⟧ x = 0#
⟦ k +x∙ p ⟧ x = k + x * ⟦ p ⟧ x

1ᵖ : Polynomial
1ᵖ = 1# +x∙ 0ᵖ

infixl 6 _+ᵖ_
_+ᵖ_ : Polynomial → Polynomial → Polynomial
0ᵖ +ᵖ q = q
p +ᵖ 0ᵖ = p
(k₁ +x∙ p) +ᵖ (k₂ +x∙ q) = (k₁ + k₂) +x∙ (p +ᵖ q)

infixl 7 _∙ᵖ_
_∙ᵖ_ : C → Polynomial → Polynomial
a ∙ᵖ 0ᵖ = 0ᵖ
a ∙ᵖ (k +x∙ p) = (a * k) +x∙ (a ∙ᵖ p)

x∙_ : Polynomial → Polynomial
x∙ p = 0# +x∙ p

𝑋 : Polynomial
𝑋 = x∙ 1ᵖ

infixl 7 _*ᵖ_
_*ᵖ_ : Polynomial → Polynomial → Polynomial
0ᵖ *ᵖ q = 0ᵖ
p *ᵖ 0ᵖ = 0ᵖ
(k₁ +x∙ p) *ᵖ (k₂ +x∙ q) = (k₁ * k₂) +x∙ (k₁ ∙ᵖ q +ᵖ k₂ ∙ᵖ p +ᵖ x∙ (p *ᵖ q))
-- (k₁ + x * p[x]) * (k₂ + x * q[x]) = k₁ * k₂ + x * (k₁ * q[x] + k₂ * p[x] + x * (p[x] * q[x]))

-ᵖ_ : Polynomial → Polynomial
-ᵖ 0ᵖ = 0ᵖ
-ᵖ (x +x∙ p) = (- x) +x∙ (-ᵖ p)

-- 1 + x + x^2
ex1 : Polynomial
ex1 = 1# +x∙ (1# +x∙ (1# +x∙ 0ᵖ))

-- 1 + x + x^2
ex2 : Polynomial
ex2 = 1ᵖ +ᵖ 𝑋 +ᵖ 𝑋 *ᵖ 𝑋
