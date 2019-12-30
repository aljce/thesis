open import Level using () renaming (_⊔_ to _⊔ˡ_)
open import Algebra using (CommutativeRing)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

open import Data.Maybe using (Maybe)
open Maybe
open import Data.List using (List)
open List
open import Data.Product using (_,_)

module AKS.Polynomial.Properties {c ℓ} (R : CommutativeRing c ℓ) where

open CommutativeRing R using (0#; 1#; _+_; _*_; -_; _-_; rawRing; ring)
  renaming (Carrier to C)
open CommutativeRing R using (_≈_; isEquivalence; setoid)
  renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open import Relation.Binary.Reasoning.Setoid setoid
open CommutativeRing R using (+-cong; +-congˡ; +-congʳ; +-identityʳ; +-identityˡ; +-assoc; +-comm)
open CommutativeRing R using (-‿inverseʳ; -‿inverseˡ; -‿cong)
open CommutativeRing R using (zeroˡ; zeroʳ; distribʳ; distribˡ; *-cong; *-congˡ; *-congʳ; *-assoc; *-comm; *-identityˡ)
open import Algebra.Properties.Ring ring using (-‿distribʳ-*; -‿+-comm; -0#≈0#)

open import Polynomial.Simple.AlmostCommutativeRing using (AlmostCommutativeRing; fromCommutativeRing)
open import Polynomial.Simple.Reflection using (solve; solveOver)

open import AKS.Polynomial.Base rawRing using (Polynomial; _≈ᵖ_; _≈ⁱ_; ≈✓; ⟦_⟧; 1ᵖ; _+ᵖ_; _∙ᵖ_; _*ᵖ_; -ᵖ_; x∙_) public
open Polynomial

open import Algebra.Structures {A = Polynomial} _≈ᵖ_ using (IsCommutativeRing; IsRing; IsAbelianGroup; IsGroup; IsMonoid; IsSemigroup; IsMagma)
open import Algebra.Definitions {A = Polynomial} _≈ᵖ_
  using (_DistributesOver_; _DistributesOverʳ_; _DistributesOverˡ_
        ; RightIdentity; LeftIdentity; Identity; Associative; Commutative
        ; RightInverse; LeftInverse; Inverse; Congruent₂; Congruent₁)

ACR : AlmostCommutativeRing c ℓ
ACR = fromCommutativeRing R (λ _ → nothing)

1ᵖ-homo : ∀ x → ⟦ 1ᵖ ⟧ x ≈ 1#
1ᵖ-homo x = begin
  1# + x * 0# ≈⟨ +-congˡ (zeroʳ x) ⟩
  1# + 0# ≈⟨ +-identityʳ 1# ⟩
  1# ∎

+ᵖ-homo : ∀ p q x → ⟦ p +ᵖ q ⟧ x ≈ ⟦ p ⟧ x + ⟦ q ⟧ x
+ᵖ-homo 0ᵖ q x = ≈-sym (+-identityˡ (⟦ q ⟧ x ))
+ᵖ-homo (k₁ +x∙ p) 0ᵖ x = ≈-sym (+-identityʳ (k₁ + x * ⟦ p ⟧ x))
+ᵖ-homo (k₁ +x∙ p) (k₂ +x∙ q) x = begin
  k₁ + k₂ + x * ⟦ p +ᵖ q ⟧ x            ≈⟨ +-congˡ (*-congˡ (+ᵖ-homo p q x)) ⟩
  k₁ + k₂ + x * (⟦ p ⟧ x + ⟦ q ⟧ x)     ≈⟨ lemma k₁ k₂ x (⟦ p ⟧ x) (⟦ q ⟧ x) ⟩
  k₁ + x * ⟦ p ⟧ x + (k₂ + x * ⟦ q ⟧ x) ∎
  where
  lemma : ∀ a b c d e → a + b + c * (d + e) ≈ a + c * d + (b + c * e)
  lemma = solve ACR

∙ᵖ-homo : ∀ a p x → ⟦ a ∙ᵖ p ⟧ x ≈ a * ⟦ p ⟧ x
∙ᵖ-homo a 0ᵖ x = ≈-sym (zeroʳ a)
∙ᵖ-homo a (k +x∙ p) x = begin
  a * k + x * ⟦ a ∙ᵖ p ⟧ x  ≈⟨ +-congˡ (*-congˡ (∙ᵖ-homo a p x)) ⟩
  a * k + x * (a * ⟦ p ⟧ x) ≈⟨ lemma a k x (⟦ p ⟧ x) ⟩
  a * (k + x * ⟦ p ⟧ x)     ∎
  where
  lemma : ∀ a b c d → a * b + c * (a * d) ≈ a * (b + c * d)
  lemma = solve ACR

x∙-homo : ∀ p x → ⟦ x∙ p ⟧ x ≈ x * ⟦ p ⟧ x
x∙-homo p x = +-identityˡ (x * ⟦ p ⟧ x)

foil : ∀ a b c d → (a + b) * (c + d) ≈ a * c + a * d + b * c + b * d
foil = solve ACR

*ᵖ-homo : ∀ p q x → ⟦ p *ᵖ q ⟧ x ≈ ⟦ p ⟧ x * ⟦ q ⟧ x
*ᵖ-homo 0ᵖ q x = ≈-sym (zeroˡ (⟦ q ⟧ x))
*ᵖ-homo (k₁ +x∙ p) 0ᵖ x = ≈-sym (zeroʳ (k₁ + x * ⟦ p ⟧ x ))
*ᵖ-homo (k₁ +x∙ p) (k₂ +x∙ q) x = begin
  k₁ * k₂ + x * ⟦ k₁ ∙ᵖ q +ᵖ k₂ ∙ᵖ p +ᵖ x∙ (p *ᵖ q) ⟧ x ≈⟨ +-congˡ (*-congˡ (+ᵖ-homo (k₁ ∙ᵖ q +ᵖ k₂ ∙ᵖ p) (x∙ (p *ᵖ q)) x)) ⟩
  k₁ * k₂ + x * (⟦ k₁ ∙ᵖ q +ᵖ k₂ ∙ᵖ p ⟧ x + ⟦ x∙ (p *ᵖ q) ⟧ x) ≈⟨ +-congˡ (*-congˡ (+-cong (+ᵖ-homo (k₁ ∙ᵖ q) (k₂ ∙ᵖ p) x) (x∙-homo (p *ᵖ q) x))) ⟩
  k₁ * k₂ + x * (⟦ k₁ ∙ᵖ q ⟧ x + ⟦ k₂ ∙ᵖ p ⟧ x + x * ⟦ p *ᵖ q ⟧ x) ≈⟨ +-congˡ (*-congˡ (+-cong (+-cong (∙ᵖ-homo k₁ q x) (∙ᵖ-homo k₂ p x)) (*-congˡ (*ᵖ-homo p q x)))) ⟩
  k₁ * k₂ + x * (k₁ * ⟦ q ⟧ x + k₂ * ⟦ p ⟧ x + (x * (⟦ p ⟧ x * ⟦ q ⟧ x))) ≈⟨ full k₁ k₂ x (⟦ p ⟧ x) (⟦ q ⟧ x) ⟩
  (k₁ + x * ⟦ p ⟧ x) * (k₂ + x * ⟦ q ⟧ x) ∎
  where
  lemma₁ : ∀ a b c d e → c * (a * e + b * d) ≈ a * (c * e) + c * d * b
  lemma₁ a b c d e = begin
    c * (a * e + b * d) ≈⟨ distribˡ c (a * e) (b * d) ⟩
    c * (a * e) + c * (b * d) ≈⟨ +-cong (≈-sym (*-assoc c a e)) (*-congˡ (*-comm b d )) ⟩
    (c * a) * e + c * (d * b) ≈⟨ +-cong (*-congʳ (*-comm c a)) (≈-sym (*-assoc c d b)) ⟩
    (a * c) * e + c * d * b   ≈⟨ +-congʳ (*-assoc a c e) ⟩
    a * (c * e) + c * d * b   ∎
  lemma₂ : ∀ c d e → c * (c * (d * e)) ≈ c * d * (c * e)
  lemma₂ c d e = begin
    c * (c * (d * e)) ≈⟨ *-congˡ (≈-sym (*-assoc c d e)) ⟩
    c * (c * d * e)   ≈⟨ *-congˡ (*-congʳ (*-comm c d)) ⟩
    c * (d * c * e)   ≈⟨ *-congˡ (*-assoc d c e) ⟩
    c * (d * (c * e)) ≈⟨ ≈-sym (*-assoc c d (c * e)) ⟩
    c * d * (c * e)   ∎
  full : ∀ a b c d e → a * b + c * (a * e + b * d + (c * (d * e))) ≈ (a + c * d) * (b + c * e)
  full a b c d e = begin
    a * b + c * (a * e + b * d + (c * (d * e)))                 ≈⟨ +-congˡ (distribˡ c (a * e + b * d) (c * (d * e))) ⟩
    a * b + (c * (a * e + b * d) + c * (c * (d * e)))           ≈⟨ +-congˡ (+-cong (lemma₁ a b c d e) (lemma₂ c d e)) ⟩
    a * b + ((a * (c * e) + (c * d) * b) + ((c * d) * (c * e))) ≈⟨ ≈-sym (+-assoc (a * b) (a * (c * e) + (c * d) * b) ((c * d) * (c * e))) ⟩
    a * b + (a * (c * e) + (c * d) * b) + (c * d) * (c * e)     ≈⟨ +-congʳ (≈-sym (+-assoc (a * b) (a * (c * e)) ((c * d) * b))) ⟩
    a * b + a * (c * e) + (c * d) * b + (c * d) * (c * e)       ≈⟨ ≈-sym (foil a (c * d) b (c * e)) ⟩
    (a + c * d) * (b + c * e)                                   ∎

-ᵖ‿homo : ∀ p x → ⟦ -ᵖ p ⟧ x ≈ - ⟦ p ⟧ x
-ᵖ‿homo 0ᵖ x = ≈-sym -0#≈0#
-ᵖ‿homo (k +x∙ p) x = begin
  - k + x * ⟦ -ᵖ p ⟧ x  ≈⟨ +-congˡ (*-congˡ (-ᵖ‿homo p x)) ⟩
  - k + x * - ⟦ p ⟧ x   ≈⟨ +-congˡ (≈-sym (-‿distribʳ-* x (⟦ p ⟧ x))) ⟩
  - k + - (x * ⟦ p ⟧ x) ≈⟨ -‿+-comm k (x * ⟦ p ⟧ x ) ⟩
  - (k + x * ⟦ p ⟧ x)   ∎

≈ᵖ-refl : Reflexive _≈ᵖ_
≈ᵖ-refl = ≈✓ λ x → ≈-refl

≈ᵖ-sym : Symmetric _≈ᵖ_
≈ᵖ-sym (≈✓ ∀x[pₓ≈qₓ]) = ≈✓ (λ x → ≈-sym (∀x[pₓ≈qₓ] x))

≈ᵖ-trans : Transitive _≈ᵖ_
≈ᵖ-trans (≈✓ ∀x[pₓ≈qₓ]) (≈✓ ∀x[qₓ≈rₓ]) = ≈✓ (λ x → ≈-trans (∀x[pₓ≈qₓ] x) (∀x[qₓ≈rₓ] x))

≈ᵖ-isEquivalence : IsEquivalence _≈ᵖ_
≈ᵖ-isEquivalence = record
  { refl = ≈ᵖ-refl
  ; sym = ≈ᵖ-sym
  ; trans = ≈ᵖ-trans
  }

≈ᵖ-setoid : Setoid c (c ⊔ˡ ℓ)
≈ᵖ-setoid = record
  { Carrier = Polynomial
  ; _≈_ = _≈ᵖ_
  ; isEquivalence = ≈ᵖ-isEquivalence
  }

-- equiv : ∀ {p q} → p ≈ᵖ q → p ≈ⁱ q
-- equiv {0ᵖ} {0ᵖ} (≈✓ ∀x[pₓ≈qₓ]) = {!!}
-- equiv {0ᵖ} {k₂ +x∙ q} (≈✓ ∀x[pₓ≈qₓ]) = {!!}
-- equiv {k₁ +x∙ p} {q} (≈✓ ∀x[pₓ≈qₓ]) = {!!}

+ᵖ-cong : Congruent₂ _+ᵖ_
+ᵖ-cong {p} {q} {r} {s} (≈✓ ∀x[pₓ≈qₓ]) (≈✓ ∀x[rₓ≈sₓ]) = ≈✓ λ x → begin
  ⟦ p +ᵖ r ⟧ x ≈⟨ +ᵖ-homo p r x ⟩
  ⟦ p ⟧ x + ⟦ r ⟧ x ≈⟨ +-cong (∀x[pₓ≈qₓ] x) (∀x[rₓ≈sₓ] x)  ⟩
  ⟦ q ⟧ x + ⟦ s ⟧ x ≈⟨ ≈-sym (+ᵖ-homo q s x) ⟩
  ⟦ q +ᵖ s ⟧ x ∎

+ᵖ-isMagma : IsMagma _+ᵖ_
+ᵖ-isMagma = record
  { isEquivalence = ≈ᵖ-isEquivalence
  ; ∙-cong = +ᵖ-cong
  }

-- open import Relation.Nullary using (Dec; yes; no)

-- module _ (≈-dec : ∀ x y → Dec (x ≈ y)) where
--   ≈ᵖ-dec : ∀ p q → Dec (p ≈ᵖ q)
--   ≈ᵖ-dec 0ᵖ 0ᵖ = yes (≈✓ λ x → ≈-refl)
--   ≈ᵖ-dec 0ᵖ (k₂ +x∙ q) = no λ 0≈k₂+x∙q → {!!}
--   ≈ᵖ-dec (x +x∙ p) q = {!!}

+ᵖ-assoc : Associative _+ᵖ_
+ᵖ-assoc p q r = ≈✓ λ x → begin
  ⟦ p +ᵖ q +ᵖ r ⟧ x ≈⟨ +ᵖ-homo (p +ᵖ q) r x ⟩
  ⟦ p +ᵖ q ⟧ x + ⟦ r ⟧ x ≈⟨ +-congʳ (+ᵖ-homo p q x) ⟩
  ⟦ p ⟧ x + ⟦ q ⟧ x + ⟦ r ⟧ x ≈⟨ +-assoc (⟦ p ⟧ x) (⟦ q ⟧ x) (⟦ r ⟧ x) ⟩
  ⟦ p ⟧ x + (⟦ q ⟧ x + ⟦ r ⟧ x) ≈⟨ +-congˡ (≈-sym (+ᵖ-homo q r x)) ⟩
  ⟦ p ⟧ x + ⟦ q +ᵖ r ⟧ x ≈⟨ ≈-sym (+ᵖ-homo p (q +ᵖ r) x) ⟩
  ⟦ p +ᵖ (q +ᵖ r) ⟧ x ∎

+ᵖ-isSemigroup : IsSemigroup _+ᵖ_
+ᵖ-isSemigroup = record
  { isMagma = +ᵖ-isMagma
  ; assoc = +ᵖ-assoc
  }

+ᵖ-comm : Commutative _+ᵖ_
+ᵖ-comm p q = ≈✓ λ x → begin
  ⟦ p +ᵖ q ⟧ x ≈⟨ +ᵖ-homo p q x ⟩
  ⟦ p ⟧ x + ⟦ q ⟧ x ≈⟨ +-comm (⟦ p ⟧ x) (⟦ q ⟧ x) ⟩
  ⟦ q ⟧ x + ⟦ p ⟧ x ≈⟨ ≈-sym (+ᵖ-homo q p x) ⟩
  ⟦ q +ᵖ p ⟧ x ∎

+ᵖ-identityˡ : LeftIdentity 0ᵖ _+ᵖ_
+ᵖ-identityˡ p = ≈✓ λ x → begin
  ⟦ 0ᵖ +ᵖ p ⟧ x ≈⟨ +ᵖ-homo 0ᵖ p x ⟩
  0# + ⟦ p ⟧ x ≈⟨ +-identityˡ (⟦ p ⟧ x) ⟩
  ⟦ p ⟧ x ∎

open import Algebra.FunctionProperties.Consequences ≈ᵖ-setoid using (comm+idˡ⇒idʳ; comm+invˡ⇒invʳ; comm+distrˡ⇒distrʳ)

+ᵖ-identityʳ : RightIdentity 0ᵖ _+ᵖ_
+ᵖ-identityʳ = comm+idˡ⇒idʳ +ᵖ-comm +ᵖ-identityˡ

+ᵖ-identity : Identity 0ᵖ _+ᵖ_
+ᵖ-identity = +ᵖ-identityˡ , +ᵖ-identityʳ

+ᵖ-isMonoid : IsMonoid _+ᵖ_ 0ᵖ
+ᵖ-isMonoid = record
  { isSemigroup = +ᵖ-isSemigroup
  ; identity = +ᵖ-identity
  }

-ᵖ‿inverseˡ : LeftInverse 0ᵖ -ᵖ_ _+ᵖ_
-ᵖ‿inverseˡ p = ≈✓ λ x → begin
  ⟦ -ᵖ p +ᵖ p ⟧ x      ≈⟨ +ᵖ-homo (-ᵖ p) p x ⟩
  ⟦ -ᵖ p ⟧ x + ⟦ p ⟧ x ≈⟨ +-congʳ (-ᵖ‿homo p x) ⟩
  - ⟦ p ⟧ x + ⟦ p ⟧ x  ≈⟨ -‿inverseˡ (⟦ p ⟧ x) ⟩
  ⟦ 0ᵖ ⟧ x             ∎

-ᵖ‿inverseʳ : RightInverse 0ᵖ -ᵖ_ _+ᵖ_
-ᵖ‿inverseʳ = comm+invˡ⇒invʳ +ᵖ-comm -ᵖ‿inverseˡ

-ᵖ‿inverse : Inverse 0ᵖ -ᵖ_ _+ᵖ_
-ᵖ‿inverse = -ᵖ‿inverseˡ , -ᵖ‿inverseʳ

-ᵖ‿cong : Congruent₁ -ᵖ_
-ᵖ‿cong {p} {q} (≈✓ ∀x[pₓ≈qₓ]) = ≈✓ λ x → begin
  ⟦ -ᵖ p ⟧ x ≈⟨ -ᵖ‿homo p x ⟩
  - ⟦ p ⟧ x  ≈⟨ -‿cong (∀x[pₓ≈qₓ] x) ⟩
  - ⟦ q ⟧ x  ≈⟨ ≈-sym (-ᵖ‿homo q x) ⟩
  ⟦ -ᵖ q ⟧ x ∎

+ᵖ-isGroup : IsGroup _+ᵖ_ 0ᵖ -ᵖ_
+ᵖ-isGroup = record
  { isMonoid = +ᵖ-isMonoid
  ; inverse = -ᵖ‿inverse
  ; ⁻¹-cong = -ᵖ‿cong
  }

+ᵖ-isAbelianGroup : IsAbelianGroup _+ᵖ_ 0ᵖ -ᵖ_
+ᵖ-isAbelianGroup = record
  { isGroup = +ᵖ-isGroup
  ; comm = +ᵖ-comm
  }

*ᵖ-cong : Congruent₂ _*ᵖ_
*ᵖ-cong {p} {q} {r} {s} (≈✓ ∀x[pₓ≈qₓ]) (≈✓ ∀x[rₓ≈sₓ]) = ≈✓ λ x → begin
  ⟦ p *ᵖ r ⟧ x ≈⟨ *ᵖ-homo p r x ⟩
  ⟦ p ⟧ x * ⟦ r ⟧ x ≈⟨ *-cong (∀x[pₓ≈qₓ] x) (∀x[rₓ≈sₓ] x)  ⟩
  ⟦ q ⟧ x * ⟦ s ⟧ x ≈⟨ ≈-sym (*ᵖ-homo q s x) ⟩
  ⟦ q *ᵖ s ⟧ x ∎

*ᵖ-isMagma : IsMagma _*ᵖ_
*ᵖ-isMagma = record
  { isEquivalence = ≈ᵖ-isEquivalence
  ; ∙-cong = *ᵖ-cong
  }

*ᵖ-assoc : Associative _*ᵖ_
*ᵖ-assoc p q r = ≈✓ λ x → begin
  ⟦ p *ᵖ q *ᵖ r ⟧ x ≈⟨ *ᵖ-homo (p *ᵖ q) r x ⟩
  ⟦ p *ᵖ q ⟧ x * ⟦ r ⟧ x ≈⟨ *-congʳ (*ᵖ-homo p q x) ⟩
  ⟦ p ⟧ x * ⟦ q ⟧ x * ⟦ r ⟧ x ≈⟨ *-assoc (⟦ p ⟧ x) (⟦ q ⟧ x) (⟦ r ⟧ x) ⟩
  ⟦ p ⟧ x * (⟦ q ⟧ x * ⟦ r ⟧ x) ≈⟨ *-congˡ (≈-sym (*ᵖ-homo q r x)) ⟩
  ⟦ p ⟧ x * ⟦ q *ᵖ r ⟧ x ≈⟨ ≈-sym (*ᵖ-homo p (q *ᵖ r) x) ⟩
  ⟦ p *ᵖ (q *ᵖ r) ⟧ x ∎

*ᵖ-isSemigroup : IsSemigroup _*ᵖ_
*ᵖ-isSemigroup = record
  { isMagma = *ᵖ-isMagma
  ; assoc = *ᵖ-assoc
  }

*ᵖ-comm : Commutative _*ᵖ_
*ᵖ-comm p q = ≈✓ λ x → begin
  ⟦ p *ᵖ q ⟧ x ≈⟨ *ᵖ-homo p q x ⟩
  ⟦ p ⟧ x * ⟦ q ⟧ x ≈⟨ *-comm (⟦ p ⟧ x) (⟦ q ⟧ x) ⟩
  ⟦ q ⟧ x * ⟦ p ⟧ x ≈⟨ ≈-sym (*ᵖ-homo q p x) ⟩
  ⟦ q *ᵖ p ⟧ x ∎

*ᵖ-identityˡ : LeftIdentity 1ᵖ _*ᵖ_
*ᵖ-identityˡ p = ≈✓ λ x → begin
  ⟦ 1ᵖ *ᵖ p ⟧ x      ≈⟨ *ᵖ-homo 1ᵖ p x ⟩
  ⟦ 1ᵖ ⟧ x * ⟦ p ⟧ x ≈⟨ *-congʳ (1ᵖ-homo x) ⟩
  1# * ⟦ p ⟧ x       ≈⟨ *-identityˡ (⟦ p ⟧ x) ⟩
  ⟦ p ⟧ x            ∎


*ᵖ-identityʳ : RightIdentity 1ᵖ _*ᵖ_
*ᵖ-identityʳ = comm+idˡ⇒idʳ *ᵖ-comm *ᵖ-identityˡ

*ᵖ-identity : Identity 1ᵖ _*ᵖ_
*ᵖ-identity = *ᵖ-identityˡ , *ᵖ-identityʳ

*ᵖ-1ᵖ-isMonoid : IsMonoid _*ᵖ_ 1ᵖ
*ᵖ-1ᵖ-isMonoid = record
  { isSemigroup = *ᵖ-isSemigroup
  ; identity = *ᵖ-identity
  }

*ᵖ-distribˡ-+ᵖ : _*ᵖ_ DistributesOverˡ _+ᵖ_
*ᵖ-distribˡ-+ᵖ p q r = ≈✓ λ x → begin
  ⟦ p *ᵖ (q +ᵖ r) ⟧ x                   ≈⟨ *ᵖ-homo p (q +ᵖ r) x ⟩
  ⟦ p ⟧ x * ⟦ q +ᵖ r ⟧ x                ≈⟨ *-congˡ (+ᵖ-homo q r x)  ⟩
  ⟦ p ⟧ x * (⟦ q ⟧ x + ⟦ r ⟧ x)         ≈⟨ distribˡ (⟦ p ⟧ x) (⟦ q ⟧ x) (⟦ r ⟧ x) ⟩
  ⟦ p ⟧ x * ⟦ q ⟧ x + ⟦ p ⟧ x * ⟦ r ⟧ x ≈⟨ +-cong (≈-sym (*ᵖ-homo p q x)) (≈-sym (*ᵖ-homo p r x)) ⟩
  ⟦ p *ᵖ q ⟧ x + ⟦ p *ᵖ r ⟧ x           ≈⟨ ≈-sym (+ᵖ-homo (p *ᵖ q) (p *ᵖ r) x) ⟩
  ⟦ p *ᵖ q +ᵖ p *ᵖ r ⟧ x                ∎


*ᵖ-distribʳ-+ᵖ : _*ᵖ_ DistributesOverʳ _+ᵖ_
*ᵖ-distribʳ-+ᵖ = comm+distrˡ⇒distrʳ +ᵖ-cong *ᵖ-comm *ᵖ-distribˡ-+ᵖ

*ᵖ-distrib-+ᵖ : _*ᵖ_ DistributesOver _+ᵖ_
*ᵖ-distrib-+ᵖ = *ᵖ-distribˡ-+ᵖ , *ᵖ-distribʳ-+ᵖ

+ᵖ-*ᵖ-isRing : IsRing _+ᵖ_ _*ᵖ_ -ᵖ_ 0ᵖ 1ᵖ
+ᵖ-*ᵖ-isRing = record
  { +-isAbelianGroup = +ᵖ-isAbelianGroup
  ; *-isMonoid = *ᵖ-1ᵖ-isMonoid
  ; distrib = *ᵖ-distrib-+ᵖ
  }

+ᵖ-*ᵖ-isCommutativeRing : IsCommutativeRing _+ᵖ_ _*ᵖ_ -ᵖ_ 0ᵖ 1ᵖ
+ᵖ-*ᵖ-isCommutativeRing = record
  { isRing = +ᵖ-*ᵖ-isRing
  ; *-comm = *ᵖ-comm
  }
