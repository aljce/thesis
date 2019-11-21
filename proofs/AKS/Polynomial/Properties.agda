open import Algebra using (CommutativeRing)

open import Data.Maybe using (Maybe)
open Maybe
open import Data.List using (List)
open List

module AKS.Polynomial.Properties {c ℓ} (R : CommutativeRing c ℓ) where

open CommutativeRing R using (0#; 1#; _+_; _*_; -_; _-_; rawRing; ring)
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

open import AKS.Polynomial.Base rawRing using (Polynomial; ⟦_⟧; _+ᵖ_; _∙ᵖ_; _*ᵖ_; -ᵖ_; x∙_) public
open Polynomial

ACR : AlmostCommutativeRing c ℓ
ACR = fromCommutativeRing R (λ _ → nothing)

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

