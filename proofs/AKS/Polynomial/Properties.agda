open import Level using () renaming (_⊔_ to _⊔ˡ_)
open import Function using (_$_; flip)

open import Function.Equivalence as FE using ()
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Setoid; IsEquivalence; Decidable; DecSetoid; IsDecEquivalence; Tri)
open import Relation.Binary.Definitions using (Recomputable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_) renaming (refl to ≡-refl; sym to ≡-sym; cong to ≡-cong; cong₂ to ≡-cong₂; setoid to ≡-setoid)
open Tri

open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)

open import Algebra.Bundles using (CommutativeRing)
open import AKS.Algebra.Bundles using (DecField; IntegralDomain)

module AKS.Polynomial.Properties {c ℓ} (F : DecField c ℓ) where

open import AKS.Nat using (ℕ; zero; suc; _<_; _≤_; lte; _≟_; _≟⁺_; _∸_; ℕ⁺; ℕ+; ⟅_⇓⟆; ⟅_⇑⟆; pred) renaming (_+_ to _+ℕ_)
open import AKS.Nat using (<-cmp; <-≤-connex; m+[n∸m]≡n; ℕ→ℕ⁺→ℕ; ⟅⇓⟆-injective; m<n⇒n∸m≢0; ≢⇒¬≟; <⇒≤; +-suc)
open import AKS.Nat using (0≤n; suc-mono-≤; ≤-reflexive; +-mono-<; module ≤-Reasoning)
open import AKS.Nat using (_⊔_; ⊔-identityʳ; ⊔-identityˡ; +-distribˡ-⊔; ⊔-least-<; m≤n⇒m⊔n≡n)
open import AKS.Nat using (Acc; acc; <-well-founded)
import Data.Nat.Properties as Nat

open import Polynomial.Simple.AlmostCommutativeRing using (AlmostCommutativeRing; fromCommutativeRing)
open import Polynomial.Simple.Reflection using (solve; solveOver)
open import Polynomial.Simple.AlmostCommutativeRing.Instances using (module Nat)
open Nat.Reflection using (∀⟨_⟩)

open DecField F
  using (0#; 1#; _+_; _*_; -_; _-_; _⁻¹; _/_)
  renaming (Carrier to C)
open DecField F
  using (C/0; _*-nonzero_; _/-nonzero_; -1#-nonzero; 0#≉1#; 1#≉0#; *-cancelˡ)
open DecField F using (_≈_; _≉_; _≈?_; setoid)
open Setoid setoid using (refl; sym; trans)
open import Relation.Binary.Reasoning.MultiSetoid
open DecField F using (ring; commutativeRing; *-commutativeMonoid)
open CommutativeRing commutativeRing using (+-assoc; +-comm; +-cong; +-congˡ; +-congʳ; +-identityˡ; +-identityʳ)
open CommutativeRing commutativeRing using (*-assoc; *-comm; *-cong; *-congˡ; *-congʳ; *-identityˡ; *-identityʳ; zeroˡ; zeroʳ)
open CommutativeRing commutativeRing using (distribˡ; distribʳ; -‿cong; -‿inverseˡ; -‿inverseʳ)
open import Algebra.Properties.Ring ring using (-‿distribˡ-*)
open import AKS.Exponentiation *-commutativeMonoid using (_^_; _^⁺_; ^-homo; ^-^⁺-homo; x^n≈x^⁺n)

open import AKS.Polynomial.Base F using
  ( Polynomialⁱ; 0ⁱ; 1ⁱ; _+x∙_; _+ⁱ_; -ⁱ_; _∙ⁱ_; _*ⁱ_; x∙_; expand; expandˢ; simplify; +ⁱ-*ⁱ-rawRing
  ; _≈ⁱ_; _≉ⁱ_; 0≈0; 0≈+; +≈0; +≈+; ≈ⁱ-refl; ≈ⁱ-sym; ≈ⁱ-trans
  ; Spine; K; _+x^_∙_; Polynomial; 0ᵖ; x^_∙_; ⟦_⟧; ⟦_⟧ˢ; _+?_; 𝐾; 𝑋; _∙𝑋^_
  ; 1ᵖ; _+ᵖ_; +ᵖ-spine; +ᵖ-spine-≡-K; +ᵖ-spine-≡; +ᵖ-spine-<; -ᵖ_; _-ᵖ_; _*ᵖ_; *ᵖ-spine; _∙ᵖ_; ∙ᵖ-spine; +ᵖ-*ᵖ-rawRing
  ; _≈ᵖ_; _≉ᵖ_; 0ᵖ≈; 0ᵖ≉; _≈ˢ_; K≈; +≈; ≈ᵖ-refl; ≈ᵖ-sym; ≈ᵖ-trans
  ; Degree; deg; degree; degreeˢ; _⊔ᵈ_; _+ᵈ_; _≤ᵈ_; -∞≤_; ≤ᵈ-refl; module ≤ᵈ-Reasoning; -∞; ⟨_⟩; degreeⁱ
  )
open import Algebra.Structures {A = Polynomialⁱ} _≈ⁱ_ using (IsCommutativeRing; IsRing; IsAbelianGroup; IsGroup; IsMonoid; IsSemigroup; IsMagma)
open import Algebra.Definitions {A = Polynomialⁱ} _≈ⁱ_ using
  ( _DistributesOver_; _DistributesOverʳ_; _DistributesOverˡ_
  ; RightIdentity; LeftIdentity; Identity; Associative; Commutative
  ; RightInverse; LeftInverse; Inverse
  ; LeftCongruent; RightCongruent; Congruent₂; Congruent₁
  )
open import AKS.Algebra.Structures using (IsNonZeroCommutativeRing; IsIntegralDomain)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)
open import AKS.Algebra.Morphism.Structures using (IsRingHomomorphism; IsRingMonomorphism)
open import AKS.Algebra.Morphism.Consequences using (module RingConsequences)

+-*-almostCommutativeRing : AlmostCommutativeRing c ℓ
+-*-almostCommutativeRing = fromCommutativeRing commutativeRing (λ _ → nothing)

expand-cong : ∀ {p} {q} → p ≈ᵖ q → expand p ≈ⁱ expand q
expand-cong 0ᵖ≈ = ≈ⁱ-refl
expand-cong (0ᵖ≉ ≡-refl p≈ˢq) = expandˢ-cong p≈ˢq
  where
  expandˢ-cong : ∀ {n} {p} {q} → p ≈ˢ q → expandˢ n p ≈ⁱ expandˢ n q
  expandˢ-cong {zero} {K c₁} {K c₂} (K≈ c₁≈c₂) = +≈+ c₁≈c₂ 0≈0
  expandˢ-cong {zero} {c₁ +x^ i ∙ p} {c₂ +x^ i ∙ q} (+≈ c₁≈c₂ ≡-refl p≈ˢq) = +≈+ c₁≈c₂ (expandˢ-cong p≈ˢq)
  expandˢ-cong {suc n} {p} {q} p≈ˢq = +≈+ refl (expandˢ-cong {n} p≈ˢq)

0≉expandˢ[≉0] : ∀ n p → 0ⁱ ≉ⁱ expandˢ n p
0≉expandˢ[≉0] zero (K c) (0≈+ c≈0 _) = contradiction c≈0 (proj₂ c)
0≉expandˢ[≉0] zero (c +x^ i ∙ p) (0≈+ c≈0 _) = contradiction c≈0 (proj₂ c)
0≉expandˢ[≉0] (suc n) p (0≈+ _ 0ⁱ≈expand) = 0≉expandˢ[≉0] n p 0ⁱ≈expand

0≉expand[≉0] : ∀ n p → 0ⁱ ≉ⁱ expand (x^ n ∙ p)
0≉expand[≉0] = 0≉expandˢ[≉0]

expand-injective : ∀ {p q} → expand p ≈ⁱ expand q → p ≈ᵖ q
expand-injective {0ᵖ} {0ᵖ} pf = ≈ᵖ-refl
expand-injective {0ᵖ} {x^ o₂ ∙ q} pf = contradiction pf          (0≉expand[≉0] o₂ q)
expand-injective {x^ o₁ ∙ p} {0ᵖ} pf = contradiction (≈ⁱ-sym pf) (0≉expand[≉0] o₁ p)
expand-injective {x^ o₁ ∙ p} {x^ o₂ ∙ q} pf = expandˢ-injective o₁ o₂ p q pf
  where
  expandˢ-injective : ∀ o₁ o₂ p q → expandˢ o₁ p ≈ⁱ expandˢ o₂ q → x^ o₁ ∙ p ≈ᵖ x^ o₂ ∙ q
  expandˢ-injective zero zero (K c₁)          (K c₂)          (+≈+ c₁≈c₂ pf) = 0ᵖ≉ ≡-refl (K≈ c₁≈c₂)
  expandˢ-injective zero zero (K c₁)          (c₂ +x^ i₂ ∙ q) (+≈+ c₁≈c₂ pf) = contradiction pf          (0≉expandˢ[≉0] _ _)
  expandˢ-injective zero zero (c₁ +x^ i₁ ∙ p) (K c₂)          (+≈+ c₁≈c₂ pf) = contradiction (≈ⁱ-sym pf) (0≉expandˢ[≉0] _ _)
  expandˢ-injective zero zero (c₁ +x^ i₁ ∙ p) (c₂ +x^ i₂ ∙ q) (+≈+ c₁≈c₂ pf) with expandˢ-injective (pred ⟅ i₁ ⇓⟆) (pred ⟅ i₂ ⇓⟆) p q pf
  ... | 0ᵖ≉ i₁≡i₂ p≈ˢq = 0ᵖ≉ ≡-refl (+≈ c₁≈c₂ (⟅⇓⟆-injective i₁≡i₂) p≈ˢq)
  expandˢ-injective zero (suc o₂) (K c₁)          q               (+≈+ c₁≈c₂ pf) = contradiction pf (0≉expandˢ[≉0] _ _)
  expandˢ-injective zero (suc o₂) (c₁ +x^ i₁ ∙ p) (K c₂)          (+≈+ c₁≈0  pf) = contradiction c₁≈0 (proj₂ c₁)
  expandˢ-injective zero (suc o₂) (c₁ +x^ i₁ ∙ p) (c₂ +x^ i₂ ∙ q) (+≈+ c₁≈0  pf) = contradiction c₁≈0 (proj₂ c₁)
  expandˢ-injective (suc o₁) zero p               (K c₂)          (+≈+ c₁≈c₂ pf) = contradiction (≈ⁱ-sym pf) (0≉expandˢ[≉0] _ _)
  expandˢ-injective (suc o₁) zero (K c₁)          (c₂ +x^ i₂ ∙ q) (+≈+ 0≈c₂  pf) = contradiction (sym 0≈c₂) (proj₂ c₂)
  expandˢ-injective (suc o₁) zero (c₁ +x^ i₁ ∙ p) (c₂ +x^ i₂ ∙ q) (+≈+ 0≈c₂  pf) = contradiction (sym 0≈c₂) (proj₂ c₂)
  expandˢ-injective (suc o₁) (suc o₂) p q (+≈+ _ pf) with expandˢ-injective o₁ o₂ p q pf
  ... | 0ᵖ≉ ≡-refl p≈ˢq = 0ᵖ≉ ≡-refl p≈ˢq

infix 4 _≈ˢ?_
_≈ˢ?_ : Decidable _≈ˢ_
(K c₁) ≈ˢ? (K c₂) with proj₁ c₁ ≈? proj₁ c₂
... | no ¬c₁≈c₂ = no λ { (K≈ c₁≈c₂) → contradiction c₁≈c₂ ¬c₁≈c₂ }
... | yes c₁≈c₂ = yes (K≈ c₁≈c₂)
(K c₁) ≈ˢ? (c₂ +x^ m ∙ q) = no λ ()
(c₁ +x^ n ∙ p) ≈ˢ? (K c₂) = no λ ()
(c₁ +x^ n ∙ p) ≈ˢ? (c₂ +x^ m ∙ q) with proj₁ c₁ ≈? proj₁ c₂
... | no ¬c₁≈c₂ = no λ { (+≈ c₁≈c₂ _ _) → contradiction c₁≈c₂ ¬c₁≈c₂ }
... | yes c₁≈c₂ with n ≟⁺ m
...   | no  n≢m = no λ { (+≈ _ n≡m _) → contradiction n≡m n≢m }
...   | yes n≡m with p ≈ˢ? q
...     | no ¬p≈ˢq = no λ { (+≈ _ _ p≈ˢq) → contradiction p≈ˢq ¬p≈ˢq }
...     | yes p≈ˢq = yes (+≈ c₁≈c₂ n≡m p≈ˢq)

infix 4 _≈ᵖ?_
_≈ᵖ?_ : Decidable _≈ᵖ_
0ᵖ ≈ᵖ? 0ᵖ = yes ≈ᵖ-refl
0ᵖ ≈ᵖ? (x^ m ∙ q) = no λ ()
(x^ n ∙ p) ≈ᵖ? 0ᵖ = no λ ()
(x^ n ∙ p) ≈ᵖ? (x^ m ∙ q) with n ≟ m
... | no  n≢m = no λ { (0ᵖ≉ n≡m _) → contradiction n≡m n≢m }
... | yes n≡m with p ≈ˢ? q
...   | no ¬p≈ˢq = no λ { (0ᵖ≉ _ p≈ˢq) → contradiction p≈ˢq ¬p≈ˢq }
...   | yes p≈ˢq = yes (0ᵖ≉ n≡m p≈ˢq)

≈ᵖ-isEquivalence : IsEquivalence _≈ᵖ_
≈ᵖ-isEquivalence = record
  { refl = ≈ᵖ-refl
  ; sym = ≈ᵖ-sym
  ; trans = ≈ᵖ-trans
  }

≈ᵖ-isDecEquivalence : IsDecEquivalence _≈ᵖ_
≈ᵖ-isDecEquivalence = record
  { isEquivalence = ≈ᵖ-isEquivalence
  ; _≟_ = _≈ᵖ?_
  }

≈ᵖ-setoid : Setoid (c ⊔ˡ ℓ) (c ⊔ˡ ℓ)
≈ᵖ-setoid = record
  { Carrier = Polynomial
  ; _≈_ = _≈ᵖ_
  ; isEquivalence = ≈ᵖ-isEquivalence
  }

≈ᵖ-decSetoid : DecSetoid (c ⊔ˡ ℓ) (c ⊔ˡ ℓ)
≈ᵖ-decSetoid = record
  { Carrier = Polynomial
  ; _≈_ = _≈ᵖ_
  ; isDecEquivalence = ≈ᵖ-isDecEquivalence
  }

≈ᵖ-recomputable : Recomputable _≈ᵖ_
≈ᵖ-recomputable {p} {q} [p≈q]₁ with p ≈ᵖ? q
... | yes [p≈q]₂ = [p≈q]₂
... | no ¬[p≈q]  = ⊥-elim (¬[p≈q] [p≈q]₁)

⟦⟧-preserves-≈ᵖ→≈ : ∀ {p q} → p ≈ᵖ q → ∀ x → ⟦ p ⟧ x ≈ ⟦ q ⟧ x
⟦⟧-preserves-≈ᵖ→≈ {0ᵖ} {0ᵖ} 0ᵖ≈ x = refl
⟦⟧-preserves-≈ᵖ→≈ {x^ n ∙ p} {x^ n ∙ q} (0ᵖ≉ ≡-refl p≈ˢq) x = *-congˡ (⟦⟧-preserves-≈ᵖ→≈ˢ p q p≈ˢq x)
  where
  ⟦⟧-preserves-≈ᵖ→≈ˢ : ∀ p q → p ≈ˢ q → ∀ x → ⟦ p ⟧ˢ x ≈ ⟦ q ⟧ˢ x
  ⟦⟧-preserves-≈ᵖ→≈ˢ (K c₁) (K c₂) (K≈ c₁≈c₂) x = c₁≈c₂
  ⟦⟧-preserves-≈ᵖ→≈ˢ (c₁ +x^ n ∙ p) (c₂ +x^ n ∙ q) (+≈ c₁≈c₂ ≡-refl p≈ˢq) x = begin⟨ setoid ⟩
    proj₁ c₁ + x ^⁺ n * ⟦ p ⟧ˢ x ≈⟨ +-cong c₁≈c₂ (*-congˡ (⟦⟧-preserves-≈ᵖ→≈ˢ p q p≈ˢq x)) ⟩
    proj₁ c₂ + x ^⁺ n * ⟦ q ⟧ˢ x ∎

_≈ⁱ?_ : Decidable _≈ⁱ_
0ⁱ ≈ⁱ? 0ⁱ = yes 0≈0
0ⁱ ≈ⁱ? (c₂ +x∙ q) with c₂ ≈? 0#
... | no  c₂≉0 = no λ { (0≈+ c₂≈0 _) → contradiction c₂≈0 c₂≉0 }
... | yes c₂≈0 with 0ⁱ ≈ⁱ? q
...   | no  0≉q = no λ { (0≈+ _ 0≈q) → contradiction 0≈q 0≉q }
...   | yes 0≈q = yes (0≈+ c₂≈0 0≈q)
(c₁ +x∙ p) ≈ⁱ? 0ⁱ with c₁ ≈? 0#
... | no  c₁≉0 = no λ { (+≈0 c₁≈0 _) → contradiction c₁≈0 c₁≉0 }
... | yes c₁≈0 with p ≈ⁱ? 0ⁱ
...   | no  p≉0 = no λ { (+≈0 _ 0≈p) → contradiction (≈ⁱ-sym 0≈p) p≉0 }
...   | yes p≈0 = yes (+≈0 c₁≈0 (≈ⁱ-sym p≈0))
(c₁ +x∙ p) ≈ⁱ? (c₂ +x∙ q) with c₁ ≈? c₂
... | no  c₁≉c₂ = no λ { (+≈+ c₁≈c₂ _) → contradiction c₁≈c₂ c₁≉c₂}
... | yes c₁≈c₂ with p ≈ⁱ? q
...   | no  p≉q = no λ { (+≈+ _ p≈q) → contradiction p≈q p≉q}
...   | yes p≈q = yes (+≈+ c₁≈c₂ p≈q)

≈ⁱ-isEquivalence : IsEquivalence _≈ⁱ_
≈ⁱ-isEquivalence = record
  { refl = ≈ⁱ-refl
  ; sym = ≈ⁱ-sym
  ; trans = ≈ⁱ-trans
  }

≈ⁱ-isDecEquivalence : IsDecEquivalence _≈ⁱ_
≈ⁱ-isDecEquivalence = record
  { isEquivalence = ≈ⁱ-isEquivalence
  ; _≟_ = _≈ⁱ?_
  }

≈ⁱ-setoid : Setoid c (c ⊔ˡ ℓ)
≈ⁱ-setoid = record
  { Carrier = Polynomialⁱ
  ; _≈_ = _≈ⁱ_
  ; isEquivalence = ≈ⁱ-isEquivalence
  }

≈ⁱ-decSetoid : DecSetoid c (c ⊔ˡ ℓ)
≈ⁱ-decSetoid = record
  { Carrier = Polynomialⁱ
  ; _≈_ = _≈ⁱ_
  ; isDecEquivalence = ≈ⁱ-isDecEquivalence
  }

≈ⁱ-recomputable : Recomputable _≈ⁱ_
≈ⁱ-recomputable {p} {q} [p≈q]₁ with p ≈ⁱ? q
... | yes [p≈q]₂ = [p≈q]₂
... | no ¬[p≈q]  = ⊥-elim (¬[p≈q] [p≈q]₁)

+ⁱ-comm : Commutative _+ⁱ_
+ⁱ-comm 0ⁱ 0ⁱ = ≈ⁱ-refl
+ⁱ-comm 0ⁱ (c₂ +x∙ q) = ≈ⁱ-refl
+ⁱ-comm (c₁ +x∙ p) 0ⁱ = ≈ⁱ-refl
+ⁱ-comm (c₁ +x∙ p) (c₂ +x∙ q) = +≈+ (+-comm c₁ c₂) (+ⁱ-comm p q)

+ⁱ-identityˡ : LeftIdentity 0ⁱ _+ⁱ_
+ⁱ-identityˡ _ = ≈ⁱ-refl

+ⁱ-identityʳ : RightIdentity 0ⁱ _+ⁱ_
+ⁱ-identityʳ 0ⁱ = ≈ⁱ-refl
+ⁱ-identityʳ (c +x∙ p) = ≈ⁱ-refl

+ⁱ-identity : Identity 0ⁱ _+ⁱ_
+ⁱ-identity = +ⁱ-identityˡ , +ⁱ-identityʳ

+ⁱ-congˡ : LeftCongruent _+ⁱ_
+ⁱ-congˡ {0ⁱ}       {p}        {q}        p≈q = p≈q
+ⁱ-congˡ {c₁ +x∙ r} {0ⁱ}       {0ⁱ}       0≈0 = ≈ⁱ-refl
+ⁱ-congˡ {c₁ +x∙ r} {0ⁱ}       {c₃ +x∙ q} (0≈+ c₃≈0 0≈q)=
  +≈+ (begin⟨ setoid ⟩ c₁ ≈⟨ sym (+-identityʳ c₁) ⟩ c₁ + 0# ≈⟨ +-congˡ (sym c₃≈0) ⟩ c₁ + c₃ ∎)
      (begin⟨ ≈ⁱ-setoid ⟩ r ≈⟨ ≈ⁱ-sym (+ⁱ-identityʳ r) ⟩ r +ⁱ 0ⁱ ≈⟨ +ⁱ-congˡ 0≈q ⟩ r +ⁱ q ∎)
+ⁱ-congˡ {c₁ +x∙ r} {c₂ +x∙ p} {0ⁱ}       (+≈0 c₂≈0 0≈p) =
  +≈+ (begin⟨ setoid ⟩ c₁ + c₂ ≈⟨ +-congˡ c₂≈0 ⟩ c₁ + 0# ≈⟨ +-identityʳ c₁ ⟩ c₁ ∎)
      (begin⟨ ≈ⁱ-setoid ⟩ r +ⁱ p ≈⟨ +ⁱ-congˡ (≈ⁱ-sym 0≈p) ⟩ r +ⁱ 0ⁱ ≈⟨ +ⁱ-identityʳ r ⟩ r ∎)
+ⁱ-congˡ {c₁ +x∙ r} {c₂ +x∙ p} {c₃ +x∙ q} (+≈+ c₂≈c₃ p≈q) = +≈+ (+-congˡ c₂≈c₃) (+ⁱ-congˡ p≈q)

+ⁱ-congʳ : RightCongruent _+ⁱ_
+ⁱ-congʳ {r} {p} {q} p≈q = begin⟨ ≈ⁱ-setoid ⟩
  p +ⁱ r ≈⟨ +ⁱ-comm p r ⟩
  r +ⁱ p ≈⟨ +ⁱ-congˡ p≈q ⟩
  r +ⁱ q ≈⟨ +ⁱ-comm r q ⟩
  q +ⁱ r ∎

+ⁱ-cong : Congruent₂ _+ⁱ_
+ⁱ-cong {p} {q} {r} {s} p≈q r≈s = begin⟨ ≈ⁱ-setoid ⟩
  p +ⁱ r ≈⟨ +ⁱ-congˡ r≈s ⟩
  p +ⁱ s ≈⟨ +ⁱ-congʳ p≈q ⟩
  q +ⁱ s ∎

+ⁱ-isMagma : IsMagma _+ⁱ_
+ⁱ-isMagma = record
  { isEquivalence = ≈ⁱ-isEquivalence
  ; ∙-cong = +ⁱ-cong
  }

+ⁱ-assoc : Associative _+ⁱ_
+ⁱ-assoc 0ⁱ q r = ≈ⁱ-refl
+ⁱ-assoc (c₁ +x∙ p) 0ⁱ r = ≈ⁱ-refl
+ⁱ-assoc (c₁ +x∙ p) (c₂ +x∙ q) 0ⁱ = ≈ⁱ-refl
+ⁱ-assoc (c₁ +x∙ p) (c₂ +x∙ q) (c₃ +x∙ r) = +≈+ (+-assoc c₁ c₂ c₃) (+ⁱ-assoc p q r )

+ⁱ-isSemigroup : IsSemigroup _+ⁱ_
+ⁱ-isSemigroup = record
  { isMagma = +ⁱ-isMagma
  ; assoc = +ⁱ-assoc
  }

open import Algebra.FunctionProperties.Consequences ≈ⁱ-setoid using (comm+idˡ⇒idʳ; comm+invˡ⇒invʳ; comm+distrˡ⇒distrʳ)

+ⁱ-isMonoid : IsMonoid _+ⁱ_ 0ⁱ
+ⁱ-isMonoid = record
  { isSemigroup = +ⁱ-isSemigroup
  ; identity = +ⁱ-identity
  }

-ⁱ‿inverseˡ : LeftInverse 0ⁱ -ⁱ_ _+ⁱ_
-ⁱ‿inverseˡ 0ⁱ = ≈ⁱ-refl
-ⁱ‿inverseˡ (c +x∙ p) = +≈0
  (begin⟨ setoid ⟩
   - 1# * c + c ≈⟨ +-congʳ (sym (-‿distribˡ-* 1# c)) ⟩
   - (1# * c) + c ≈⟨ +-congʳ (-‿cong (*-identityˡ c)) ⟩
   - c + c ≈⟨ -‿inverseˡ c ⟩
   0# ∎
  ) (≈ⁱ-sym (-ⁱ‿inverseˡ p))

-ⁱ‿inverseʳ : RightInverse 0ⁱ -ⁱ_ _+ⁱ_
-ⁱ‿inverseʳ = comm+invˡ⇒invʳ +ⁱ-comm -ⁱ‿inverseˡ

-ⁱ‿inverse : Inverse 0ⁱ -ⁱ_ _+ⁱ_
-ⁱ‿inverse = -ⁱ‿inverseˡ , -ⁱ‿inverseʳ

∙ⁱ-cong : ∀ {c₁ c₂} {p q} → c₁ ≈ c₂ → p ≈ⁱ q → c₁ ∙ⁱ p ≈ⁱ c₂ ∙ⁱ q
∙ⁱ-cong {c₁} {c₂} {0ⁱ}       {0ⁱ}       c₁≈c₂ 0≈0 = 0≈0
∙ⁱ-cong {c₁} {c₂} {0ⁱ}       {c₄ +x∙ q} c₁≈c₂ (0≈+ c₄≈0 0≈q) = 0≈+ (begin⟨ setoid ⟩ c₂ * c₄ ≈⟨ *-congˡ c₄≈0 ⟩ c₂ * 0# ≈⟨ zeroʳ c₂ ⟩ 0# ∎) (∙ⁱ-cong c₁≈c₂ 0≈q)
∙ⁱ-cong {c₁} {c₂} {c₃ +x∙ p} {0ⁱ}       c₁≈c₂ (+≈0 c₃≈0 0≈p) = +≈0 (begin⟨ setoid ⟩ c₁ * c₃ ≈⟨ *-congˡ c₃≈0 ⟩ c₁ * 0# ≈⟨ zeroʳ c₁ ⟩ 0# ∎) (∙ⁱ-cong (sym c₁≈c₂) 0≈p)
∙ⁱ-cong {c₁} {c₂} {c₃ +x∙ p} {c₄ +x∙ q} c₁≈c₂ (+≈+ c₃≈c₄ p≈q) = +≈+ (*-cong c₁≈c₂ c₃≈c₄) (∙ⁱ-cong c₁≈c₂ p≈q)

-ⁱ‿cong : Congruent₁ (-ⁱ_)
-ⁱ‿cong = ∙ⁱ-cong refl

+ⁱ-isGroup : IsGroup _+ⁱ_ 0ⁱ (-ⁱ_)
+ⁱ-isGroup = record
  { isMonoid = +ⁱ-isMonoid
  ; inverse = -ⁱ‿inverse
  ; ⁻¹-cong = -ⁱ‿cong
  }

+ⁱ-isAbelianGroup : IsAbelianGroup _+ⁱ_ 0ⁱ (-ⁱ_)
+ⁱ-isAbelianGroup = record
  { isGroup = +ⁱ-isGroup
  ; comm = +ⁱ-comm
  }

*ⁱ-comm : Commutative _*ⁱ_
*ⁱ-comm 0ⁱ 0ⁱ = ≈ⁱ-refl
*ⁱ-comm 0ⁱ (c₂ +x∙ q) = ≈ⁱ-refl
*ⁱ-comm (c₁ +x∙ p) 0ⁱ = ≈ⁱ-refl
*ⁱ-comm (c₁ +x∙ p) (c₂ +x∙ q) = +≈+ (*-comm c₁ c₂) (+ⁱ-cong (+ⁱ-comm (c₁ ∙ⁱ q) (c₂ ∙ⁱ p)) (+≈+ refl (*ⁱ-comm p q)))

0≈0∙p : ∀ p → 0ⁱ ≈ⁱ 0# ∙ⁱ p
0≈0∙p 0ⁱ = 0≈0
0≈0∙p (c +x∙ p) = 0≈+ (zeroˡ c) (0≈0∙p p)

*ⁱ-zeroʳ : ∀ r → r *ⁱ 0ⁱ ≈ⁱ 0ⁱ
*ⁱ-zeroʳ 0ⁱ = ≈ⁱ-refl
*ⁱ-zeroʳ (c +x∙ p) = ≈ⁱ-refl

*ⁱ-congˡ : LeftCongruent _*ⁱ_
*ⁱ-congˡ {0ⁱ}       {p}        {q}        p≈q = ≈ⁱ-refl
*ⁱ-congˡ {c₁ +x∙ r} {0ⁱ}       {0ⁱ}       0≈0 = ≈ⁱ-refl
*ⁱ-congˡ {c₁ +x∙ r} {0ⁱ}       {c₃ +x∙ q} (0≈+ c₃≈0 0≈q) = 0≈+ (begin⟨ setoid ⟩ c₁ * c₃ ≈⟨ *-congˡ c₃≈0 ⟩ c₁ * 0# ≈⟨ zeroʳ c₁ ⟩ 0# ∎) $
  begin⟨ ≈ⁱ-setoid ⟩
  c₁ ∙ⁱ 0ⁱ +ⁱ 0ⁱ +ⁱ 0ⁱ               ≈⟨ +ⁱ-cong (+ⁱ-cong (∙ⁱ-cong (refl {c₁}) 0≈q) (0≈0∙p r)) (0≈+ refl (≈ⁱ-sym (*ⁱ-zeroʳ r))) ⟩
  c₁ ∙ⁱ q +ⁱ 0# ∙ⁱ r +ⁱ x∙ (r *ⁱ 0ⁱ) ≈⟨ +ⁱ-cong (+ⁱ-congˡ {c₁ ∙ⁱ q} (∙ⁱ-cong (sym c₃≈0) ≈ⁱ-refl)) (+≈+ refl (*ⁱ-congˡ {r} 0≈q)) ⟩
  c₁ ∙ⁱ q +ⁱ c₃ ∙ⁱ r +ⁱ x∙ (r *ⁱ q)  ∎
*ⁱ-congˡ {c₁ +x∙ r} {c₂ +x∙ p} {0ⁱ}       (+≈0 c₂≈0 0≈p) = +≈0 (begin⟨ setoid ⟩ c₁ * c₂ ≈⟨ *-congˡ c₂≈0 ⟩ c₁ * 0# ≈⟨ zeroʳ c₁ ⟩ 0# ∎) $
  begin⟨ ≈ⁱ-setoid ⟩
  c₁ ∙ⁱ 0ⁱ +ⁱ 0ⁱ +ⁱ 0ⁱ               ≈⟨ +ⁱ-cong (+ⁱ-cong (∙ⁱ-cong (refl {c₁}) 0≈p) (0≈0∙p r)) (0≈+ refl (≈ⁱ-sym (*ⁱ-zeroʳ r))) ⟩
  c₁ ∙ⁱ p +ⁱ 0# ∙ⁱ r +ⁱ x∙ (r *ⁱ 0ⁱ) ≈⟨ +ⁱ-cong (+ⁱ-congˡ {c₁ ∙ⁱ p} (∙ⁱ-cong (sym c₂≈0) ≈ⁱ-refl)) (+≈+ refl (*ⁱ-congˡ {r} 0≈p)) ⟩
  c₁ ∙ⁱ p +ⁱ c₂ ∙ⁱ r +ⁱ x∙ (r *ⁱ p)  ∎
*ⁱ-congˡ {c₁ +x∙ r} {c₂ +x∙ p} {c₃ +x∙ q} (+≈+ c₂≈c₃ p≈q) = +≈+ (*-congˡ c₂≈c₃) (+ⁱ-cong (+ⁱ-cong (∙ⁱ-cong refl p≈q) (∙ⁱ-cong c₂≈c₃ ≈ⁱ-refl)) (+≈+ refl (*ⁱ-congˡ p≈q)))

*ⁱ-congʳ : RightCongruent _*ⁱ_
*ⁱ-congʳ {r} {p} {q} p≈q = begin⟨ ≈ⁱ-setoid ⟩
  p *ⁱ r ≈⟨ *ⁱ-comm p r ⟩
  r *ⁱ p ≈⟨ *ⁱ-congˡ p≈q ⟩
  r *ⁱ q ≈⟨ *ⁱ-comm r q ⟩
  q *ⁱ r ∎

*ⁱ-cong : Congruent₂ _*ⁱ_
*ⁱ-cong {p} {q} {r} {s} p≈q r≈s = begin⟨ ≈ⁱ-setoid ⟩
  p *ⁱ r ≈⟨ *ⁱ-congˡ r≈s ⟩
  p *ⁱ s ≈⟨ *ⁱ-congʳ p≈q ⟩
  q *ⁱ s ∎

*ⁱ-isMagma : IsMagma _*ⁱ_
*ⁱ-isMagma = record
  { isEquivalence = ≈ⁱ-isEquivalence
  ; ∙-cong = *ⁱ-cong
  }

∙ⁱ-distrib-+ⁱ : ∀ c p q → c ∙ⁱ (p +ⁱ q) ≈ⁱ c ∙ⁱ p +ⁱ c ∙ⁱ q
∙ⁱ-distrib-+ⁱ c₁ 0ⁱ q = ≈ⁱ-refl
∙ⁱ-distrib-+ⁱ c₁ (c₂ +x∙ p) 0ⁱ = ≈ⁱ-refl
∙ⁱ-distrib-+ⁱ c₁ (c₂ +x∙ p) (c₃ +x∙ q) = +≈+ (distribˡ c₁ c₂ c₃) (∙ⁱ-distrib-+ⁱ c₁ p q)

∙ⁱ-distrib-* : ∀ c₁ c₂ p → (c₁ * c₂) ∙ⁱ p ≈ⁱ c₁ ∙ⁱ (c₂ ∙ⁱ p)
∙ⁱ-distrib-* c₁ c₂ 0ⁱ = ≈ⁱ-refl
∙ⁱ-distrib-* c₁ c₂ (c₃ +x∙ p) = +≈+ (*-assoc c₁ c₂ c₃) (∙ⁱ-distrib-* c₁ c₂ p)

x∙-distrib-+ⁱ : ∀ p q → x∙ (p +ⁱ q) ≈ⁱ x∙ p +ⁱ x∙ q
x∙-distrib-+ⁱ 0ⁱ q = +≈+ (sym (+-identityʳ 0#)) (+ⁱ-identityˡ q)
x∙-distrib-+ⁱ (c₁ +x∙ p) 0ⁱ = +≈+ (sym (+-identityʳ 0#)) ≈ⁱ-refl
x∙-distrib-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) = +≈+ (sym (+-identityʳ 0#)) ≈ⁱ-refl

∙ⁱ-distrib-+ : ∀ c₁ c₂ p → (c₁ + c₂) ∙ⁱ p ≈ⁱ c₁ ∙ⁱ p +ⁱ c₂ ∙ⁱ p
∙ⁱ-distrib-+ c₁ c₂ 0ⁱ = ≈ⁱ-refl
∙ⁱ-distrib-+ c₁ c₂ (c₃ +x∙ p) = +≈+ (distribʳ c₃ c₁ c₂) (∙ⁱ-distrib-+ c₁ c₂ p)

*ⁱ-distribˡ-+ⁱ : _*ⁱ_ DistributesOverˡ _+ⁱ_
*ⁱ-distribˡ-+ⁱ 0ⁱ p q = ≈ⁱ-refl
*ⁱ-distribˡ-+ⁱ (c₁ +x∙ r) 0ⁱ q = ≈ⁱ-refl
*ⁱ-distribˡ-+ⁱ (c₁ +x∙ r) (c₂ +x∙ p) 0ⁱ = ≈ⁱ-refl
*ⁱ-distribˡ-+ⁱ (c₁ +x∙ r) (c₂ +x∙ p) (c₃ +x∙ q) = +≈+ (distribˡ c₁ c₂ c₃) $ begin⟨ ≈ⁱ-setoid ⟩
  c₁ ∙ⁱ (p +ⁱ q) +ⁱ (c₂ + c₃) ∙ⁱ r +ⁱ x∙ (r *ⁱ (p +ⁱ q))                         ≈⟨ +ⁱ-cong (+ⁱ-cong (∙ⁱ-distrib-+ⁱ c₁ p q) (∙ⁱ-distrib-+ c₂ c₃ r)) (+≈+ refl (*ⁱ-distribˡ-+ⁱ r p q)) ⟩
  (c₁ ∙ⁱ p +ⁱ c₁ ∙ⁱ q) +ⁱ (c₂ ∙ⁱ r +ⁱ c₃ ∙ⁱ r) +ⁱ x∙ (r *ⁱ p +ⁱ r *ⁱ q)          ≈⟨ +ⁱ-cong (≈ⁱ-sym (+ⁱ-assoc (c₁ ∙ⁱ p +ⁱ c₁ ∙ⁱ q) _ _)) (x∙-distrib-+ⁱ (r *ⁱ p) (r *ⁱ q)) ⟩
  ((c₁ ∙ⁱ p +ⁱ c₁ ∙ⁱ q) +ⁱ c₂ ∙ⁱ r) +ⁱ c₃ ∙ⁱ r +ⁱ (x∙ (r *ⁱ p) +ⁱ x∙ (r *ⁱ q))   ≈⟨ final (c₁ ∙ⁱ p) _ _ _ _ _ ⟩
  c₁ ∙ⁱ p +ⁱ c₂ ∙ⁱ r +ⁱ x∙ (r *ⁱ p) +ⁱ (c₁ ∙ⁱ q +ⁱ c₃ ∙ⁱ r +ⁱ x∙ (r *ⁱ q))       ∎
  where
  final : ∀ a b c d x y → ((a +ⁱ b) +ⁱ c) +ⁱ d +ⁱ (x +ⁱ y) ≈ⁱ a +ⁱ c +ⁱ x +ⁱ (b +ⁱ d +ⁱ y)
  final a b c d x y = begin⟨ ≈ⁱ-setoid ⟩
    (((a +ⁱ b) +ⁱ c) +ⁱ d) +ⁱ (x +ⁱ y) ≈⟨ +ⁱ-congʳ (+ⁱ-congʳ (+ⁱ-assoc a b c)) ⟩
    ((a +ⁱ (b +ⁱ c)) +ⁱ d) +ⁱ (x +ⁱ y) ≈⟨ +ⁱ-congʳ (+ⁱ-congʳ (+ⁱ-congˡ {a} (+ⁱ-comm b c))) ⟩
    ((a +ⁱ (c +ⁱ b)) +ⁱ d) +ⁱ (x +ⁱ y) ≈⟨ +ⁱ-congʳ (+ⁱ-assoc a (c +ⁱ b) d) ⟩
    (a +ⁱ ((c +ⁱ b) +ⁱ d)) +ⁱ (x +ⁱ y) ≈⟨ +ⁱ-congʳ (+ⁱ-congˡ {a} (+ⁱ-assoc c b d)) ⟩
    (a +ⁱ (c +ⁱ (b +ⁱ d))) +ⁱ (x +ⁱ y) ≈⟨ +ⁱ-congʳ (≈ⁱ-sym (+ⁱ-assoc a c (b +ⁱ d))) ⟩
    ((a +ⁱ c) +ⁱ (b +ⁱ d)) +ⁱ (x +ⁱ y) ≈⟨ +ⁱ-assoc (a +ⁱ c) (b +ⁱ d) (x +ⁱ y) ⟩
    (a +ⁱ c) +ⁱ ((b +ⁱ d) +ⁱ (x +ⁱ y)) ≈⟨ +ⁱ-congˡ {a +ⁱ c} (≈ⁱ-sym (+ⁱ-assoc (b +ⁱ d) x y)) ⟩
    (a +ⁱ c) +ⁱ (((b +ⁱ d) +ⁱ x) +ⁱ y) ≈⟨ +ⁱ-congˡ {a +ⁱ c} (+ⁱ-congʳ (+ⁱ-comm (b +ⁱ d) x)) ⟩
    (a +ⁱ c) +ⁱ ((x +ⁱ (b +ⁱ d)) +ⁱ y) ≈⟨ +ⁱ-congˡ {a +ⁱ c} (+ⁱ-assoc x (b +ⁱ d) y) ⟩
    (a +ⁱ c) +ⁱ (x +ⁱ ((b +ⁱ d) +ⁱ y)) ≈⟨ ≈ⁱ-sym (+ⁱ-assoc (a +ⁱ c) x (b +ⁱ d +ⁱ y)) ⟩
    ((a +ⁱ c) +ⁱ x) +ⁱ ((b +ⁱ d) +ⁱ y) ∎

*ⁱ-distribʳ-+ⁱ : _*ⁱ_ DistributesOverʳ _+ⁱ_
*ⁱ-distribʳ-+ⁱ = comm+distrˡ⇒distrʳ +ⁱ-cong *ⁱ-comm *ⁱ-distribˡ-+ⁱ

*ⁱ-distrib-+ⁱ : _*ⁱ_ DistributesOver _+ⁱ_
*ⁱ-distrib-+ⁱ = *ⁱ-distribˡ-+ⁱ , *ⁱ-distribʳ-+ⁱ

open import AKS.Unsafe using (TODO)

+x∙-distribʳ-*ⁱ : ∀ c p q → (c +x∙ p) *ⁱ q ≈ⁱ c ∙ⁱ q +ⁱ x∙ (p *ⁱ q)
+x∙-distribʳ-*ⁱ c₁ p 0ⁱ = 0≈+ refl (≈ⁱ-sym (*ⁱ-zeroʳ p))
+x∙-distribʳ-*ⁱ c₁ p (c₂ +x∙ q) = +≈+ (sym (+-identityʳ (c₁ * c₂))) $ begin⟨ ≈ⁱ-setoid ⟩
  (c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p) +ⁱ x∙ (p *ⁱ q) ≈⟨ +ⁱ-congˡ (+≈+ refl (*ⁱ-comm p q)) ⟩
  (c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p) +ⁱ x∙ (q *ⁱ p) ≈⟨ +ⁱ-assoc (c₁ ∙ⁱ q) (c₂ ∙ⁱ p) (x∙ (q *ⁱ p)) ⟩
  c₁ ∙ⁱ q +ⁱ (c₂ ∙ⁱ p +ⁱ x∙ (q *ⁱ p)) ≈⟨ +ⁱ-congˡ (≈ⁱ-sym (+x∙-distribʳ-*ⁱ c₂ q p)) ⟩
  c₁ ∙ⁱ q +ⁱ (c₂ +x∙ q) *ⁱ p          ≈⟨ +ⁱ-congˡ (*ⁱ-comm (c₂ +x∙ q) p) ⟩
  c₁ ∙ⁱ q +ⁱ p *ⁱ (c₂ +x∙ q)          ∎

+x∙-distribˡ-*ⁱ : ∀ c p q → p *ⁱ (c +x∙ q) ≈ⁱ c ∙ⁱ p +ⁱ x∙ (p *ⁱ q)
+x∙-distribˡ-*ⁱ c p q = begin⟨ ≈ⁱ-setoid ⟩
  p *ⁱ (c +x∙ q)        ≈⟨ *ⁱ-comm p (c +x∙ q) ⟩
  (c +x∙ q) *ⁱ p        ≈⟨ +x∙-distribʳ-*ⁱ c q p ⟩
  c ∙ⁱ p +ⁱ x∙ (q *ⁱ p) ≈⟨ +ⁱ-congˡ (+≈+ refl (*ⁱ-comm q p)) ⟩
  c ∙ⁱ p +ⁱ x∙ (p *ⁱ q) ∎

x∙-distrib-*ⁱ : ∀ p q → x∙ (p *ⁱ q) ≈ⁱ p *ⁱ (x∙ q)
x∙-distrib-*ⁱ 0ⁱ q = +≈0 refl ≈ⁱ-refl
x∙-distrib-*ⁱ (c₁ +x∙ p) 0ⁱ = +≈+ (sym (zeroʳ c₁)) $ begin⟨ ≈ⁱ-setoid ⟩
  0ⁱ +ⁱ 0ⁱ                ≈⟨ +ⁱ-cong (0≈0∙p p) (0≈+ refl (≈ⁱ-sym (*ⁱ-zeroʳ p))) ⟩
  0# ∙ⁱ p +ⁱ x∙ (p *ⁱ 0ⁱ) ∎
x∙-distrib-*ⁱ (c₁ +x∙ p) (c₂ +x∙ q) = +≈+ (sym (zeroʳ c₁)) $ begin⟨ ≈ⁱ-setoid ⟩
  (c₁ * c₂) +x∙ (c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q))            ≈⟨ TODO ⟩
  (c₁ * c₂) +x∙ (c₁ ∙ⁱ q +ⁱ (c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q)))          ≈⟨ +≈+ refl (+ⁱ-congˡ (≈ⁱ-sym (+x∙-distribˡ-*ⁱ c₂ p q))) ⟩
  (c₁ * c₂) +x∙ (c₁ ∙ⁱ q +ⁱ p *ⁱ (c₂ +x∙ q))                   ≈⟨ TODO ⟩
  ((c₁ * c₂) +x∙ (c₁ ∙ⁱ q)) +ⁱ 0# ∙ⁱ p +ⁱ x∙ (p *ⁱ (c₂ +x∙ q)) ∎


*ⁱ-assoc : Associative _*ⁱ_
*ⁱ-assoc 0ⁱ q r = ≈ⁱ-refl
*ⁱ-assoc (c₁ +x∙ p) 0ⁱ r = ≈ⁱ-refl
*ⁱ-assoc (c₁ +x∙ p) (c₂ +x∙ q) 0ⁱ = ≈ⁱ-refl
*ⁱ-assoc (c₁ +x∙ p) (c₂ +x∙ q) (c₃ +x∙ r) = +≈+ (*-assoc c₁ c₂ c₃) $ begin⟨ ≈ⁱ-setoid ⟩
  (c₁ * c₂) ∙ⁱ r +ⁱ  c₃ ∙ⁱ (c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q)) +ⁱ x∙ ((c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q)) *ⁱ r)
  ≈⟨ TODO ⟩
  c₁ ∙ⁱ (c₂ ∙ⁱ r) +ⁱ (c₃ ∙ⁱ (c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p) +ⁱ c₃ ∙ⁱ (x∙ (p *ⁱ q))) +ⁱ x∙ ((c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q)) *ⁱ r)
  ≈⟨ TODO ⟩
  c₁ ∙ⁱ (c₂ ∙ⁱ r +ⁱ c₃ ∙ⁱ q +ⁱ x∙ (q *ⁱ r)) +ⁱ c₂ * c₃ ∙ⁱ p +ⁱ x∙ (p *ⁱ (c₂ ∙ⁱ r +ⁱ c₃ ∙ⁱ q +ⁱ x∙ (q *ⁱ r))) ∎

*ⁱ-isSemigroup : IsSemigroup _*ⁱ_
*ⁱ-isSemigroup = record
  { isMagma = *ⁱ-isMagma
  ; assoc = *ⁱ-assoc
  }

∙ⁱ-identity : ∀ p → 1# ∙ⁱ p ≈ⁱ p
∙ⁱ-identity 0ⁱ = ≈ⁱ-refl
∙ⁱ-identity (c +x∙ p) = +≈+ (*-identityˡ c) (∙ⁱ-identity p)

*ⁱ-identityˡ : LeftIdentity 1ⁱ _*ⁱ_
*ⁱ-identityˡ 0ⁱ = ≈ⁱ-refl
*ⁱ-identityˡ (c +x∙ p) = +≈+ (*-identityˡ c) $ begin⟨ ≈ⁱ-setoid ⟩
  1# ∙ⁱ p +ⁱ 0ⁱ +ⁱ (0# +x∙ 0ⁱ) ≈⟨ +ⁱ-cong (+ⁱ-congʳ (∙ⁱ-identity p)) (+≈0 refl 0≈0) ⟩
  p +ⁱ 0ⁱ +ⁱ 0ⁱ                ≈⟨ +ⁱ-identityʳ (p +ⁱ 0ⁱ) ⟩
  p +ⁱ 0ⁱ                      ≈⟨ +ⁱ-identityʳ p ⟩
  p ∎

*ⁱ-identityʳ : RightIdentity 1ⁱ _*ⁱ_
*ⁱ-identityʳ = comm+idˡ⇒idʳ *ⁱ-comm *ⁱ-identityˡ

*ⁱ-identity : Identity 1ⁱ _*ⁱ_
*ⁱ-identity = *ⁱ-identityˡ , *ⁱ-identityʳ

*ⁱ-1ⁱ-isMonoid : IsMonoid _*ⁱ_ 1ⁱ
*ⁱ-1ⁱ-isMonoid = record
  { isSemigroup = *ⁱ-isSemigroup
  ; identity = *ⁱ-identity
  }

+ⁱ-*ⁱ-isRing : IsRing _+ⁱ_ _*ⁱ_ -ⁱ_ 0ⁱ 1ⁱ
+ⁱ-*ⁱ-isRing = record
  { +-isAbelianGroup = +ⁱ-isAbelianGroup
  ; *-isMonoid = *ⁱ-1ⁱ-isMonoid
  ; distrib = *ⁱ-distrib-+ⁱ
  }

+ⁱ-*ⁱ-isCommutativeRing : IsCommutativeRing _+ⁱ_ _*ⁱ_ -ⁱ_ 0ⁱ 1ⁱ
+ⁱ-*ⁱ-isCommutativeRing = record
  { isRing = +ⁱ-*ⁱ-isRing
  ; *-comm = *ⁱ-comm
  }

+ⁱ-*ⁱ-commutativeRing : CommutativeRing c (c ⊔ˡ ℓ)
+ⁱ-*ⁱ-commutativeRing = record { isCommutativeRing = +ⁱ-*ⁱ-isCommutativeRing }

open CommutativeRing +ⁱ-*ⁱ-commutativeRing using () renaming (+-rawMonoid to +ⁱ-rawMonoid; zeroˡ to *ⁱ-zeroˡ)

+ⁱ-*ⁱ-almostCommutativeRing : AlmostCommutativeRing c (c ⊔ˡ ℓ)
+ⁱ-*ⁱ-almostCommutativeRing = fromCommutativeRing +ⁱ-*ⁱ-commutativeRing isZero
  where
  isZero : ∀ x → Maybe (0ⁱ ≈ⁱ x)
  isZero 0ⁱ = just ≈ⁱ-refl
  isZero (_ +x∙ _) = nothing


0ⁱ≉1ⁱ : 0ⁱ ≉ⁱ 1ⁱ
0ⁱ≉1ⁱ (0≈+ 1#≈0# _) = contradiction 1#≈0# 1#≉0#

+ⁱ-*ⁱ-isNonZeroCommutativeRing : IsNonZeroCommutativeRing Polynomialⁱ _≈ⁱ_ _+ⁱ_ _*ⁱ_ -ⁱ_ 0ⁱ 1ⁱ
+ⁱ-*ⁱ-isNonZeroCommutativeRing = record
  { isCommutativeRing = +ⁱ-*ⁱ-isCommutativeRing
  ; 0#≉1# = 0ⁱ≉1ⁱ
  }

+≉0 : ∀ {c} {p} → c ≈ 0# → c +x∙ p ≉ⁱ 0ⁱ → p ≉ⁱ 0ⁱ
+≉0 c≈0 c+x∙p≉0ⁱ p≈0 = contradiction (+≈0 c≈0 (≈ⁱ-sym p≈0)) c+x∙p≉0ⁱ

*ⁱ-cancelˡ-lemma₁ : ∀ c₁ p c₂ q → c₁ ≈ 0# → 0ⁱ ≈ⁱ c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q) → p *ⁱ 0ⁱ ≈ⁱ p *ⁱ (c₂ +x∙ q)
*ⁱ-cancelˡ-lemma₁ c₁ p c₂ q c₁≈0 pf = begin⟨ ≈ⁱ-setoid ⟩
  p *ⁱ 0ⁱ                           ≈⟨ *ⁱ-zeroʳ p ⟩
  0ⁱ                                ≈⟨ pf ⟩
  c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q) ≈⟨ +ⁱ-congʳ (+ⁱ-congʳ (∙ⁱ-cong c₁≈0 (≈ⁱ-refl {q}))) ⟩
  0# ∙ⁱ q +ⁱ c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q) ≈⟨ +ⁱ-congʳ (+ⁱ-congʳ (≈ⁱ-sym (0≈0∙p q))) ⟩
  0ⁱ +ⁱ c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q)      ≈⟨ ≈ⁱ-sym (+x∙-distribˡ-*ⁱ c₂ p q) ⟩
  p *ⁱ (c₂ +x∙ q)                   ∎

*ⁱ-cancelˡ-lemma₂ : ∀ c₁ p c₂ q → c₂ ≈ 0# → 0ⁱ ≈ⁱ c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q) → (c₁ +x∙ p) *ⁱ 0ⁱ ≈ⁱ (c₁ +x∙ p) *ⁱ q
*ⁱ-cancelˡ-lemma₂ c₁ p c₂ q c₂≈0 pf = begin⟨ ≈ⁱ-setoid ⟩
  (c₁ +x∙ p) *ⁱ 0ⁱ                  ≈⟨ pf ⟩
  c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q) ≈⟨ +ⁱ-congʳ (+ⁱ-congˡ {c₁ ∙ⁱ q} (∙ⁱ-cong c₂≈0 ≈ⁱ-refl)) ⟩
  c₁ ∙ⁱ q +ⁱ 0# ∙ⁱ p +ⁱ x∙ (p *ⁱ q) ≈⟨ +ⁱ-congʳ (+ⁱ-congˡ {c₁ ∙ⁱ q} (≈ⁱ-sym (0≈0∙p p))) ⟩
  c₁ ∙ⁱ q +ⁱ 0ⁱ +ⁱ x∙ (p *ⁱ q)      ≈⟨ +ⁱ-congʳ (+ⁱ-identityʳ (c₁ ∙ⁱ q)) ⟩
  c₁ ∙ⁱ q +ⁱ x∙ (p *ⁱ q)            ≈⟨ ≈ⁱ-sym (+x∙-distribʳ-*ⁱ c₁ p q) ⟩
  (c₁ +x∙ p) *ⁱ q ∎


*ⁱ-cancelˡ : ∀ p {q r} → p ≉ⁱ 0ⁱ → p *ⁱ q ≈ⁱ p *ⁱ r → q ≈ⁱ r
*ⁱ-cancelˡ 0ⁱ         {q}        {r}        p≉0 p*q≈p*r = contradiction ≈ⁱ-refl p≉0
*ⁱ-cancelˡ (c₁ +x∙ p) {0ⁱ}       {0ⁱ}       p≉0 p*q≈p*r = ≈ⁱ-refl
*ⁱ-cancelˡ (c₁ +x∙ p) {0ⁱ}       {c₃ +x∙ r} p≉0 (0≈+ c₁*c₃≈0 pf) with c₁ ≈? 0#
... | yes c₁≈0 = *ⁱ-cancelˡ p (+≉0 c₁≈0 p≉0) (*ⁱ-cancelˡ-lemma₁ c₁ p c₃ r c₁≈0 pf)
... | no  c₁≉0 = 0≈+ c₃≈0 $ *ⁱ-cancelˡ (c₁ +x∙ p) p≉0 (*ⁱ-cancelˡ-lemma₂ c₁ p c₃ r c₃≈0 pf)
  where
  c₃≈0 = *-cancelˡ c₁ c₁≉0 $ begin⟨ setoid ⟩ c₁ * c₃ ≈⟨ c₁*c₃≈0 ⟩ 0# ≈⟨ sym (zeroʳ c₁) ⟩ c₁ * 0# ∎
*ⁱ-cancelˡ (c₁ +x∙ p) {c₂ +x∙ q} {0ⁱ}       p≉0 (+≈0 c₁*c₂≈0 pf) with c₁ ≈? 0#
... | yes c₁≈0 = *ⁱ-cancelˡ p (+≉0 c₁≈0 p≉0) (≈ⁱ-sym (*ⁱ-cancelˡ-lemma₁ c₁ p c₂ q c₁≈0 pf) )
... | no  c₁≉0 = +≈0 c₂≈0 $ ≈ⁱ-sym (*ⁱ-cancelˡ (c₁ +x∙ p) {q} {0ⁱ} p≉0 (≈ⁱ-sym (*ⁱ-cancelˡ-lemma₂ c₁ p c₂ q c₂≈0 pf)))
  where
  c₂≈0 = *-cancelˡ c₁ c₁≉0 $ begin⟨ setoid ⟩ c₁ * c₂ ≈⟨ c₁*c₂≈0 ⟩ 0# ≈⟨ sym (zeroʳ c₁) ⟩ c₁ * 0# ∎
*ⁱ-cancelˡ (c₁ +x∙ p) {c₂ +x∙ q} {c₃ +x∙ r} p≉0 (+≈+ c₁*c₂≈c₁*c₃ pf) with c₁ ≈? 0#
... | yes c₁≈0 = *ⁱ-cancelˡ p (+≉0 c₁≈0 p≉0) $ begin⟨ ≈ⁱ-setoid ⟩
  0ⁱ +ⁱ p *ⁱ (c₂ +x∙ q)               ≈⟨ +ⁱ-cong (0≈0∙p q) (+x∙-distribˡ-*ⁱ c₂ p q) ⟩
  0# ∙ⁱ q +ⁱ (c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q)) ≈⟨ +ⁱ-congʳ (∙ⁱ-cong (sym c₁≈0) (≈ⁱ-refl {q})) ⟩
  c₁ ∙ⁱ q +ⁱ (c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q)) ≈⟨ ≈ⁱ-sym (+ⁱ-assoc (c₁ ∙ⁱ q) _ _) ⟩
  (c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p) +ⁱ x∙ (p *ⁱ q) ≈⟨ pf ⟩
  (c₁ ∙ⁱ r +ⁱ c₃ ∙ⁱ p) +ⁱ x∙ (p *ⁱ r) ≈⟨ +ⁱ-assoc (c₁ ∙ⁱ r) _ _ ⟩
  c₁ ∙ⁱ r +ⁱ (c₃ ∙ⁱ p +ⁱ x∙ (p *ⁱ r)) ≈⟨ +ⁱ-congʳ (∙ⁱ-cong c₁≈0 (≈ⁱ-refl {r})) ⟩
  0# ∙ⁱ r +ⁱ (c₃ ∙ⁱ p +ⁱ x∙ (p *ⁱ r)) ≈⟨ +ⁱ-cong (≈ⁱ-sym (0≈0∙p r)) (≈ⁱ-sym (+x∙-distribˡ-*ⁱ c₃ p r)) ⟩
  0ⁱ +ⁱ p *ⁱ (c₃ +x∙ r)               ∎
... | no  c₁≉0 = +≈+ c₂≈c₃ $ *ⁱ-cancelˡ (c₁ +x∙ p) p≉0 $ begin⟨ ≈ⁱ-setoid ⟩
  0ⁱ +ⁱ (c₁ +x∙ p) *ⁱ q                                 ≈⟨ +ⁱ-cong (≈ⁱ-sym (-ⁱ‿inverseˡ (c₂ ∙ⁱ p))) (+x∙-distribʳ-*ⁱ c₁ p q) ⟩
  (-ⁱ (c₂ ∙ⁱ p) +ⁱ c₂ ∙ⁱ p) +ⁱ (c₁ ∙ⁱ q +ⁱ x∙ (p *ⁱ q)) ≈⟨ lemma (-ⁱ (c₂ ∙ⁱ p)) (c₂ ∙ⁱ p) (c₁ ∙ⁱ q) (x∙ (p *ⁱ q)) ⟩
  -ⁱ (c₂ ∙ⁱ p) +ⁱ ((c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p) +ⁱ x∙ (p *ⁱ q)) ≈⟨ +ⁱ-cong (-ⁱ‿cong (∙ⁱ-cong c₂≈c₃ (≈ⁱ-refl {p}))) pf ⟩
  -ⁱ (c₃ ∙ⁱ p) +ⁱ ((c₁ ∙ⁱ r +ⁱ c₃ ∙ⁱ p) +ⁱ x∙ (p *ⁱ r)) ≈⟨ ≈ⁱ-sym (lemma (-ⁱ (c₃ ∙ⁱ p)) (c₃ ∙ⁱ p) (c₁ ∙ⁱ r) (x∙ (p *ⁱ r))) ⟩
  (-ⁱ (c₃ ∙ⁱ p) +ⁱ c₃ ∙ⁱ p) +ⁱ (c₁ ∙ⁱ r +ⁱ x∙ (p *ⁱ r)) ≈⟨ +ⁱ-cong (-ⁱ‿inverseˡ (c₃ ∙ⁱ p)) (≈ⁱ-sym (+x∙-distribʳ-*ⁱ c₁ p r)) ⟩
  0ⁱ +ⁱ (c₁ +x∙ p) *ⁱ r                                 ∎
  where
  c₂≈c₃ = *-cancelˡ c₁ c₁≉0 c₁*c₂≈c₁*c₃
  lemma : ∀ a b c d → (a +ⁱ b) +ⁱ (c +ⁱ d) ≈ⁱ a +ⁱ ((c +ⁱ b) +ⁱ d)
  lemma = solve +ⁱ-*ⁱ-almostCommutativeRing

+ⁱ-*ⁱ-isIntegralDomain : IsIntegralDomain Polynomialⁱ _≈ⁱ_ _+ⁱ_ _*ⁱ_ -ⁱ_ 0ⁱ 1ⁱ
+ⁱ-*ⁱ-isIntegralDomain = record
  { isNonZeroCommutativeRing = +ⁱ-*ⁱ-isNonZeroCommutativeRing
  ; *-cancelˡ = *ⁱ-cancelˡ
  }

+ⁱ-*ⁱ-integralDomain : IntegralDomain c (c ⊔ˡ ℓ)
+ⁱ-*ⁱ-integralDomain = record { isIntegralDomain = +ⁱ-*ⁱ-isIntegralDomain }

expandˢ-+x^-lemma : ∀ o n c p → expandˢ o (c +x^ n ∙ p) ≈ⁱ expandˢ o (K c) +ⁱ expandˢ (o +ℕ ⟅ n ⇓⟆) p
expandˢ-+x^-lemma zero (ℕ+ n) c₁ p = begin⟨ ≈ⁱ-setoid ⟩
  proj₁ c₁        +x∙ expandˢ n p ≈⟨ +≈+ (sym (+-identityʳ (proj₁ c₁))) ≈ⁱ-refl ⟩
  (proj₁ c₁ + 0#) +x∙ expandˢ n p ∎
expandˢ-+x^-lemma (suc o) n c₁ p = begin⟨ ≈ⁱ-setoid ⟩
  expandˢ (suc o) (c₁ +x^ n ∙ p) ≈⟨ +≈+ (sym (+-identityʳ 0#)) (expandˢ-+x^-lemma o n c₁ p) ⟩
  expandˢ (suc o) (K c₁) +ⁱ expandˢ (suc (o +ℕ ⟅ n ⇓⟆)) p ∎

expandˢ-≡-cong : ∀ {o₁ o₂} {p} → o₁ ≡ o₂ → expandˢ o₁ p ≈ⁱ expandˢ o₂ p
expandˢ-≡-cong ≡-refl = ≈ⁱ-refl

expandˢ-raise₁ : ∀ n o₁ p o₂ q → 0ⁱ ≈ⁱ expandˢ o₁ p +ⁱ expandˢ o₂ q → 0ⁱ ≈ⁱ expandˢ (n +ℕ o₁) p +ⁱ expandˢ (n +ℕ o₂) q
expandˢ-raise₁ zero    o₁ p o₂ q pf = pf
expandˢ-raise₁ (suc n) o₁ p o₂ q pf = 0≈+ (+-identityʳ 0#) (expandˢ-raise₁ n o₁ p o₂ q pf)

expandˢ-raise₂ : ∀ n o₁ r o₂ p o₃ q → expandˢ o₁ r ≈ⁱ expandˢ o₂ p +ⁱ expandˢ o₃ q → expandˢ (n +ℕ o₁) r ≈ⁱ expandˢ (n +ℕ o₂) p +ⁱ expandˢ (n +ℕ o₃) q
expandˢ-raise₂ zero    o₁ r o₂ p o₃ q pf = pf
expandˢ-raise₂ (suc n) o₁ r o₂ p o₃ q pf = +≈+ (sym (+-identityʳ 0#)) (expandˢ-raise₂ n o₁ r o₂ p o₃ q pf)


expandˢ-+ᵖ-spine-≡-K-homo-lemma₁ : ∀ o c₁ c₂ → proj₁ c₁ + proj₁ c₂ ≈ 0# → 0ⁱ ≈ⁱ expandˢ o (K c₁) +ⁱ expandˢ o (K c₂)
expandˢ-+ᵖ-spine-≡-K-homo-lemma₁ zero c₁ c₂ c₁+c₂≈0 = 0≈+ c₁+c₂≈0 0≈0
expandˢ-+ᵖ-spine-≡-K-homo-lemma₁ (suc o) c₁ c₂ c₁+c₂≈0 = 0≈+ (+-identityʳ 0#) (expandˢ-+ᵖ-spine-≡-K-homo-lemma₁ o c₁ c₂ c₁+c₂≈0)

expandˢ-+ᵖ-spine-≡-K-homo-lemma₂ : ∀ o c₁ c₂ c₁+c₂≉0 → expandˢ o (K (proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0)) ≈ⁱ expandˢ o (K c₁) +ⁱ expandˢ o (K c₂)
expandˢ-+ᵖ-spine-≡-K-homo-lemma₂ zero c₁ c₂ c₁+c₂≉0 = ≈ⁱ-refl
expandˢ-+ᵖ-spine-≡-K-homo-lemma₂ (suc o) c₁ c₂ c₁+c₂≉0 = +≈+ (sym (+-identityʳ 0#)) (expandˢ-+ᵖ-spine-≡-K-homo-lemma₂ o c₁ c₂ c₁+c₂≉0)

expand-+ᵖ-spine-≡-K-homo : ∀ o c p → expand (+ᵖ-spine-≡-K o c p) ≈ⁱ expandˢ o (K c) +ⁱ expandˢ o p
expand-+ᵖ-spine-≡-K-homo o c₁ (K c₂) with proj₁ c₁ + proj₁ c₂ ≈? 0#
... | yes c₁+c₂≈0 = expandˢ-+ᵖ-spine-≡-K-homo-lemma₁ o c₁ c₂ c₁+c₂≈0
... | no  c₁+c₂≉0 = expandˢ-+ᵖ-spine-≡-K-homo-lemma₂ o c₁ c₂ c₁+c₂≉0
expand-+ᵖ-spine-≡-K-homo o c₁ (c₂ +x^ n₂ ∙ p) with proj₁ c₁ + proj₁ c₂ ≈? 0#
... | yes c₁+c₂≈0 = begin⟨ ≈ⁱ-setoid ⟩
  expandˢ (o +ℕ ⟅ n₂ ⇓⟆) p                                           ≈⟨ ≈ⁱ-sym (+ⁱ-identityˡ (expandˢ (o +ℕ ⟅ n₂ ⇓⟆) p)) ⟩
  0ⁱ +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) p                                     ≈⟨ +ⁱ-congʳ (expandˢ-+ᵖ-spine-≡-K-homo-lemma₁ o c₁ c₂ c₁+c₂≈0) ⟩
  (expandˢ o (K c₁) +ⁱ expandˢ o (K c₂)) +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) p ≈⟨ +ⁱ-assoc (expandˢ o (K c₁)) (expandˢ o (K c₂)) (expandˢ (o +ℕ ⟅ n₂ ⇓⟆) p) ⟩
  expandˢ o (K c₁) +ⁱ (expandˢ o (K c₂) +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) p) ≈⟨ +ⁱ-congˡ (≈ⁱ-sym (expandˢ-+x^-lemma o n₂ c₂ p)) ⟩
  expandˢ o (K c₁) +ⁱ expandˢ o (c₂ +x^ n₂ ∙ p) ∎
... | no  c₁+c₂≉0 = begin⟨ ≈ⁱ-setoid ⟩
  expandˢ o ((proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0) +x^ n₂ ∙ p)                    ≈⟨ expandˢ-+x^-lemma o n₂ (proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0) p ⟩
  expandˢ o (K (proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0)) +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) p ≈⟨ +ⁱ-congʳ (expandˢ-+ᵖ-spine-≡-K-homo-lemma₂ o c₁ c₂ c₁+c₂≉0) ⟩
  (expandˢ o (K c₁) +ⁱ expandˢ o (K c₂)) +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) p        ≈⟨ +ⁱ-assoc (expandˢ o (K c₁)) (expandˢ o (K c₂)) (expandˢ (o +ℕ ⟅ n₂ ⇓⟆) p)  ⟩
  expandˢ o (K c₁) +ⁱ (expandˢ o (K c₂) +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) p)        ≈⟨ +ⁱ-congˡ (≈ⁱ-sym (expandˢ-+x^-lemma o n₂ c₂ p)) ⟩
  expandˢ o (K c₁) +ⁱ expandˢ o (c₂ +x^ n₂ ∙ p)          ∎

expand-+ᵖ-spine-≡-homo : ∀ o p q → expand (+ᵖ-spine-≡ o p q) ≈ⁱ expandˢ o p +ⁱ expandˢ o q
expand-+ᵖ-spine-<-homo : ∀ o₁ p o₂ q o₁<o₂ → expand (+ᵖ-spine-< o₁ p o₂ q o₁<o₂) ≈ⁱ expandˢ o₁ p +ⁱ expandˢ o₂ q
expand-+ᵖ-spine-homo   : ∀ o₁ p o₂ q → expand (+ᵖ-spine o₁ p o₂ q) ≈ⁱ expandˢ o₁ p +ⁱ expandˢ o₂ q

expand-+ᵖ-spine-≡-homo-permute : ∀ a b x y → (a +ⁱ b) +ⁱ (x +ⁱ y) ≈ⁱ (a +ⁱ x) +ⁱ (b +ⁱ y)
expand-+ᵖ-spine-≡-homo-permute = solve +ⁱ-*ⁱ-almostCommutativeRing

expand-+ᵖ-spine-≡-homo o (K c₁) q = expand-+ᵖ-spine-≡-K-homo o c₁ q
expand-+ᵖ-spine-≡-homo o (c₁ +x^ n₁ ∙ p) (K c₂) = begin⟨ ≈ⁱ-setoid ⟩
  expand (+ᵖ-spine-≡-K o c₂ (c₁ +x^ n₁ ∙ p))    ≈⟨ expand-+ᵖ-spine-≡-K-homo o c₂ (c₁ +x^ n₁ ∙ p) ⟩
  expandˢ o (K c₂) +ⁱ expandˢ o (c₁ +x^ n₁ ∙ p) ≈⟨ +ⁱ-comm (expandˢ o (K c₂)) (expandˢ o (c₁ +x^ n₁ ∙ p)) ⟩
  expandˢ o (c₁ +x^ n₁ ∙ p) +ⁱ expandˢ o (K c₂) ∎
expand-+ᵖ-spine-≡-homo o (c₁ +x^ n₁ ∙ p) (c₂ +x^ n₂ ∙ q) with proj₁ c₁ + proj₁ c₂ ≈? 0#
... | yes c₁+c₂≈0 = begin⟨ ≈ⁱ-setoid ⟩
  expand (+ᵖ-spine (o +ℕ ⟅ n₁ ⇓⟆) p (o +ℕ ⟅ n₂ ⇓⟆) q)                                              ≈⟨ expand-+ᵖ-spine-homo (o +ℕ ⟅ n₁ ⇓⟆) p (o +ℕ ⟅ n₂ ⇓⟆) q ⟩
  expandˢ (o +ℕ ⟅ n₁ ⇓⟆) p +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) q                                             ≈⟨ ≈ⁱ-sym (+ⁱ-identityˡ (expandˢ (o +ℕ ⟅ n₁ ⇓⟆) p +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) q)) ⟩
  0ⁱ +ⁱ (expandˢ (o +ℕ ⟅ n₁ ⇓⟆) p +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) q)                                     ≈⟨ +ⁱ-congʳ (expandˢ-+ᵖ-spine-≡-K-homo-lemma₁ o c₁ c₂ c₁+c₂≈0) ⟩
  (expandˢ o (K c₁) +ⁱ expandˢ o (K c₂)) +ⁱ (expandˢ (o +ℕ ⟅ n₁ ⇓⟆) p +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) q) ≈⟨ expand-+ᵖ-spine-≡-homo-permute (expandˢ o (K c₁)) (expandˢ o (K c₂)) _ _ ⟩
  (expandˢ o (K c₁) +ⁱ expandˢ (o +ℕ ⟅ n₁ ⇓⟆) p) +ⁱ (expandˢ o (K c₂) +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) q) ≈⟨ +ⁱ-cong (≈ⁱ-sym (expandˢ-+x^-lemma o n₁ c₁ p)) (≈ⁱ-sym (expandˢ-+x^-lemma o n₂ c₂ q)) ⟩
  expandˢ o (c₁ +x^ n₁ ∙ p) +ⁱ expandˢ o (c₂ +x^ n₂ ∙ q)                                           ∎
  where
... | no c₁+c₂≉0  with +ᵖ-spine ⟅ n₁ ⇓⟆ p ⟅ n₂ ⇓⟆ q | expand-+ᵖ-spine-homo ⟅ n₁ ⇓⟆ p ⟅ n₂ ⇓⟆ q
...   | 0ᵖ | pf = begin⟨ ≈ⁱ-setoid ⟩
  expandˢ o (K (proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0))                                                     ≈⟨ ≈ⁱ-sym (+ⁱ-identityʳ _) ⟩
  expandˢ o (K (proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0)) +ⁱ 0ⁱ                                               ≈⟨ +ⁱ-cong (expandˢ-+ᵖ-spine-≡-K-homo-lemma₂ o c₁ c₂ c₁+c₂≉0) (expandˢ-raise₁ o ⟅ n₁ ⇓⟆ p ⟅ n₂ ⇓⟆ q pf) ⟩
  (expandˢ o (K c₁) +ⁱ expandˢ o (K c₂)) +ⁱ (expandˢ (o +ℕ ⟅ n₁ ⇓⟆) p +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) q) ≈⟨ expand-+ᵖ-spine-≡-homo-permute (expandˢ o (K c₁)) (expandˢ o (K c₂)) _ _ ⟩
  (expandˢ o (K c₁) +ⁱ expandˢ (o +ℕ ⟅ n₁ ⇓⟆) p) +ⁱ (expandˢ o (K c₂) +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) q) ≈⟨ +ⁱ-cong (≈ⁱ-sym (expandˢ-+x^-lemma o n₁ c₁ p)) (≈ⁱ-sym (expandˢ-+x^-lemma o n₂ c₂ q)) ⟩
  expandˢ o (c₁ +x^ n₁ ∙ p) +ⁱ expandˢ o (c₂ +x^ n₂ ∙ q)                                           ∎
...   | x^ zero   ∙ r | pf = begin⟨ ≈ⁱ-setoid ⟩
  expand (+ᵖ-spine-≡-K o (proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0) r)                                        ≈⟨ expand-+ᵖ-spine-≡-K-homo o (proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0) r ⟩
  expandˢ o (K (proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0)) +ⁱ expandˢ o r                                     ≈⟨ +ⁱ-cong (expandˢ-+ᵖ-spine-≡-K-homo-lemma₂ o c₁ c₂ c₁+c₂≉0) (expandˢ-≡-cong (≡-sym (Nat.+-identityʳ o))) ⟩
  (expandˢ o (K c₁) +ⁱ expandˢ o (K c₂)) +ⁱ expandˢ (o +ℕ 0) r                                     ≈⟨ +ⁱ-congˡ (expandˢ-raise₂ o 0 r ⟅ n₁ ⇓⟆ p ⟅ n₂ ⇓⟆ q pf) ⟩
  (expandˢ o (K c₁) +ⁱ expandˢ o (K c₂)) +ⁱ (expandˢ (o +ℕ ⟅ n₁ ⇓⟆) p +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) q) ≈⟨ expand-+ᵖ-spine-≡-homo-permute (expandˢ o (K c₁)) (expandˢ o (K c₂)) _ _ ⟩
  (expandˢ o (K c₁) +ⁱ expandˢ (o +ℕ ⟅ n₁ ⇓⟆) p) +ⁱ (expandˢ o (K c₂) +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) q) ≈⟨ +ⁱ-cong (≈ⁱ-sym (expandˢ-+x^-lemma o n₁ c₁ p)) (≈ⁱ-sym (expandˢ-+x^-lemma o n₂ c₂ q)) ⟩
  expandˢ o (c₁ +x^ n₁ ∙ p) +ⁱ expandˢ o (c₂ +x^ n₂ ∙ q)                                           ∎
...   | x^ suc n₃ ∙ r | pf = begin⟨ ≈ⁱ-setoid ⟩
  expandˢ o ((proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0) +x^ ⟅ suc n₃ ⇑⟆ ∙ r)                                  ≈⟨ expandˢ-+x^-lemma o ⟅ suc n₃ ⇑⟆ (proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0) r ⟩
  expandˢ o (K (proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0)) +ⁱ expandˢ (o +ℕ suc n₃) r                         ≈⟨ +ⁱ-congʳ (expandˢ-+ᵖ-spine-≡-K-homo-lemma₂ o c₁ c₂ c₁+c₂≉0) ⟩
  (expandˢ o (K c₁) +ⁱ expandˢ o (K c₂)) +ⁱ expandˢ (o +ℕ suc n₃) r                                ≈⟨ +ⁱ-congˡ (expandˢ-raise₂ o (suc n₃) r ⟅ n₁ ⇓⟆ p ⟅ n₂ ⇓⟆ q pf) ⟩
  (expandˢ o (K c₁) +ⁱ expandˢ o (K c₂)) +ⁱ (expandˢ (o +ℕ ⟅ n₁ ⇓⟆) p +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) q) ≈⟨ expand-+ᵖ-spine-≡-homo-permute (expandˢ o (K c₁)) (expandˢ o (K c₂)) _ _ ⟩
  (expandˢ o (K c₁) +ⁱ expandˢ (o +ℕ ⟅ n₁ ⇓⟆) p) +ⁱ (expandˢ o (K c₂) +ⁱ expandˢ (o +ℕ ⟅ n₂ ⇓⟆) q) ≈⟨ +ⁱ-cong (≈ⁱ-sym (expandˢ-+x^-lemma o n₁ c₁ p)) (≈ⁱ-sym (expandˢ-+x^-lemma o n₂ c₂ q)) ⟩
  expandˢ o (c₁ +x^ n₁ ∙ p) +ⁱ expandˢ o (c₂ +x^ n₂ ∙ q)                                           ∎

expand-+ᵖ-spine-<-homo o₁ (K c₁) o₂ q o₁<o₂ = begin⟨ ≈ⁱ-setoid ⟩
  expandˢ o₁ (c₁ +x^ ⟅ o₂ ∸ o₁ ⇑⟆ ∙ q)                     ≈⟨ expandˢ-+x^-lemma o₁ ⟅ o₂ ∸ o₁ ⇑⟆ c₁ q ⟩
  expandˢ o₁ (K c₁) +ⁱ expandˢ (o₁ +ℕ ⟅ ⟅ o₂ ∸ o₁ ⇑⟆ ⇓⟆) q ≈⟨ +ⁱ-congˡ (expandˢ-≡-cong lemma) ⟩
  expandˢ o₁ (K c₁) +ⁱ expandˢ o₂ q                        ∎
  where
  lemma : o₁ +ℕ ⟅ ⟅ o₂ ∸ o₁ ⇑⟆ ⇓⟆ ≡ o₂
  lemma = begin⟨ ≡-setoid ℕ ⟩
    o₁ +ℕ ⟅ ⟅ o₂ ∸ o₁ ⇑⟆ ⇓⟆ ≡⟨ ≡-cong (λ x → o₁ +ℕ x) (ℕ→ℕ⁺→ℕ (o₂ ∸ o₁) {≢⇒¬≟ (m<n⇒n∸m≢0 o₁<o₂)}) ⟩
    o₁ +ℕ (o₂ ∸ o₁)         ≡⟨ m+[n∸m]≡n {o₁} {o₂} (<⇒≤ o₁<o₂) ⟩
    o₂ ∎
expand-+ᵖ-spine-<-homo o₁ (c₁ +x^ n₁ ∙ p) o₂ q o₁<o₂ with +ᵖ-spine ⟅ n₁ ⇓⟆ p (o₂ ∸ o₁) q | expand-+ᵖ-spine-homo ⟅ n₁ ⇓⟆ p (o₂ ∸ o₁) q
... | 0ᵖ | pf = begin⟨ ≈ⁱ-setoid ⟩
  expandˢ o₁ (K c₁)                                                               ≈⟨ ≈ⁱ-sym (+ⁱ-identityʳ (expandˢ o₁ (K c₁))) ⟩
  expandˢ o₁ (K c₁) +ⁱ 0ⁱ                                                         ≈⟨ +ⁱ-congˡ (expandˢ-raise₁ o₁ ⟅ n₁ ⇓⟆ p (o₂ ∸ o₁) q pf) ⟩
  expandˢ o₁ (K c₁) +ⁱ (expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p +ⁱ expandˢ (o₁ +ℕ (o₂ ∸ o₁)) q) ≈⟨ ≈ⁱ-sym (+ⁱ-assoc (expandˢ o₁ (K c₁)) _ _) ⟩
  (expandˢ o₁ (K c₁) +ⁱ expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p) +ⁱ expandˢ (o₁ +ℕ (o₂ ∸ o₁)) q ≈⟨ +ⁱ-cong (≈ⁱ-sym (expandˢ-+x^-lemma o₁ n₁ c₁ p)) (expandˢ-≡-cong (m+[n∸m]≡n (<⇒≤ o₁<o₂))) ⟩
  expandˢ o₁ (c₁ +x^ n₁ ∙ p) +ⁱ expandˢ o₂ q                                       ∎
... | x^ zero   ∙ r | pf = begin⟨ ≈ⁱ-setoid ⟩
  expand (+ᵖ-spine-≡-K o₁ c₁ r)                                                   ≈⟨ expand-+ᵖ-spine-≡-K-homo o₁ c₁ r ⟩
  expandˢ o₁ (K c₁) +ⁱ expandˢ o₁ r                                               ≈⟨ +ⁱ-congˡ (expandˢ-≡-cong (≡-sym (Nat.+-identityʳ o₁))) ⟩
  expandˢ o₁ (K c₁) +ⁱ expandˢ (o₁ +ℕ 0) r                                        ≈⟨ +ⁱ-congˡ (expandˢ-raise₂ o₁ 0 r ⟅ n₁ ⇓⟆ p (o₂ ∸ o₁) q pf) ⟩
  expandˢ o₁ (K c₁) +ⁱ (expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p +ⁱ expandˢ (o₁ +ℕ (o₂ ∸ o₁)) q) ≈⟨ ≈ⁱ-sym (+ⁱ-assoc (expandˢ o₁ (K c₁)) _ _) ⟩
  (expandˢ o₁ (K c₁) +ⁱ expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p) +ⁱ expandˢ (o₁ +ℕ (o₂ ∸ o₁)) q ≈⟨ +ⁱ-cong (≈ⁱ-sym (expandˢ-+x^-lemma o₁ n₁ c₁ p)) (expandˢ-≡-cong (m+[n∸m]≡n (<⇒≤ o₁<o₂))) ⟩
  expandˢ o₁ (c₁ +x^ n₁ ∙ p) +ⁱ expandˢ o₂ q                                       ∎
... | x^ suc o₃ ∙ r | pf = begin⟨ ≈ⁱ-setoid ⟩
  expandˢ o₁ (c₁ +x^ ⟅ suc o₃ ⇑⟆ ∙ r)                                             ≈⟨ expandˢ-+x^-lemma o₁ ⟅ suc o₃ ⇑⟆ c₁ r ⟩
  expandˢ o₁ (K c₁) +ⁱ expandˢ (o₁ +ℕ suc o₃) r                                   ≈⟨ +ⁱ-congˡ (expandˢ-raise₂ o₁ (suc o₃) r ⟅ n₁ ⇓⟆ p (o₂ ∸ o₁) q pf) ⟩
  expandˢ o₁ (K c₁) +ⁱ (expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p +ⁱ expandˢ (o₁ +ℕ (o₂ ∸ o₁)) q) ≈⟨ ≈ⁱ-sym (+ⁱ-assoc (expandˢ o₁ (K c₁)) _ _) ⟩
  (expandˢ o₁ (K c₁) +ⁱ expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p) +ⁱ expandˢ (o₁ +ℕ (o₂ ∸ o₁)) q ≈⟨ +ⁱ-cong (≈ⁱ-sym (expandˢ-+x^-lemma o₁ n₁ c₁ p)) (expandˢ-≡-cong (m+[n∸m]≡n (<⇒≤ o₁<o₂))) ⟩
  expandˢ o₁ (c₁ +x^ n₁ ∙ p) +ⁱ expandˢ o₂ q                                       ∎

expand-+ᵖ-spine-homo o₁ p o₂ q with <-cmp o₁ o₂
... | tri< o₁<o₂ _ _  = expand-+ᵖ-spine-<-homo o₁ p o₂ q o₁<o₂
... | tri≈ _ ≡-refl _ = expand-+ᵖ-spine-≡-homo o₁ p q
... | tri> _ _ o₁>o₂  = begin⟨ ≈ⁱ-setoid ⟩
  expand (+ᵖ-spine-< o₂ q o₁ p o₁>o₂) ≈⟨ expand-+ᵖ-spine-<-homo o₂ q o₁ p o₁>o₂ ⟩
  expandˢ o₂ q +ⁱ expandˢ o₁ p        ≈⟨ +ⁱ-comm (expandˢ o₂ q) (expandˢ o₁ p) ⟩
  expandˢ o₁ p +ⁱ expandˢ o₂ q        ∎

expand-+ᵖ-homo : ∀ p q → expand (p +ᵖ q) ≈ⁱ expand p +ⁱ expand q
expand-+ᵖ-homo 0ᵖ q = ≈ⁱ-refl
expand-+ᵖ-homo (x^ o₁ ∙ p) 0ᵖ = ≈ⁱ-sym (+ⁱ-identityʳ (expand (x^ o₁ ∙ p)))
expand-+ᵖ-homo (x^ o₁ ∙ p) (x^ o₂ ∙ q) = expand-+ᵖ-spine-homo o₁ p o₂ q

expandˢ-*ᵖ-K-lemma : ∀ o₁ o₂ c₁ c₂ → expandˢ (o₁ +ℕ o₂) (K (c₁ *-nonzero c₂)) ≈ⁱ expandˢ o₁ (K c₁) *ⁱ expandˢ o₂ (K c₂)
expandˢ-*ᵖ-K-lemma zero zero c₁ c₂ = +≈+ refl (0≈+ refl 0≈0)
expandˢ-*ᵖ-K-lemma zero (suc o₂) c₁ c₂ = +≈+ (sym (zeroʳ (proj₁ c₁))) $ begin⟨ ≈ⁱ-setoid ⟩
  expandˢ o₂ (K (c₁ *-nonzero c₂))                              ≈⟨ expandˢ-*ᵖ-K-lemma zero o₂ c₁ c₂ ⟩
  (proj₁ c₁ +x∙ 0ⁱ) *ⁱ expandˢ o₂ (K c₂)                        ≈⟨ +x∙-distribʳ-*ⁱ (proj₁ c₁) 0ⁱ (expandˢ o₂ (K c₂)) ⟩
  proj₁ c₁ ∙ⁱ expandˢ o₂ (K c₂) +ⁱ x∙ (0ⁱ *ⁱ expandˢ o₂ (K c₂)) ≈⟨ ≈ⁱ-refl ⟩
  proj₁ c₁ ∙ⁱ expandˢ o₂ (K c₂) +ⁱ x∙ 0ⁱ                        ≈⟨ +ⁱ-congʳ (≈ⁱ-sym (+ⁱ-identityʳ (proj₁ c₁ ∙ⁱ expandˢ o₂ (K c₂)))) ⟩
  proj₁ c₁ ∙ⁱ expandˢ o₂ (K c₂) +ⁱ 0ⁱ +ⁱ x∙ 0ⁱ                  ∎

expandˢ-*ᵖ-K-lemma (suc o₁) o₂ c₁ c₂ = begin⟨ ≈ⁱ-setoid ⟩
  0# +x∙ expandˢ (o₁ +ℕ o₂) (K (c₁ *-nonzero c₂))  ≈⟨ +≈+ refl (expandˢ-*ᵖ-K-lemma o₁ o₂ c₁ c₂) ⟩
  0# +x∙ (expandˢ o₁ (K c₁) *ⁱ expandˢ o₂ (K c₂))  ≈⟨ ≈ⁱ-refl ⟩
  0ⁱ +ⁱ x∙ (expandˢ o₁ (K c₁) *ⁱ expandˢ o₂ (K c₂)) ≈⟨ +ⁱ-congʳ (0≈0∙p (expandˢ o₂ (K c₂))) ⟩
  0# ∙ⁱ expandˢ o₂ (K c₂) +ⁱ x∙ (expandˢ o₁ (K c₁) *ⁱ expandˢ o₂ (K c₂)) ≈⟨ ≈ⁱ-sym (+x∙-distribʳ-*ⁱ 0# _ _) ⟩
  (0# +x∙ expandˢ o₁ (K c₁)) *ⁱ expandˢ o₂ (K c₂)  ∎

expandˢ-∙ᵖ-spine-homo : ∀ o₁ c o₂ p → expandˢ (o₁ +ℕ o₂) (∙ᵖ-spine c p) ≈ⁱ expandˢ o₁ (K c) *ⁱ expandˢ o₂ p
expandˢ-∙ᵖ-spine-homo o₁ c₁ o₂ (K c₂) = expandˢ-*ᵖ-K-lemma o₁ o₂ c₁ c₂
expandˢ-∙ᵖ-spine-homo o₁ c₁ o₂ (c₂ +x^ n₂ ∙ q) = begin⟨ ≈ⁱ-setoid ⟩
  expandˢ (o₁ +ℕ o₂) ((c₁ *-nonzero c₂) +x^ n₂ ∙ ∙ᵖ-spine c₁ q)                                ≈⟨ expandˢ-+x^-lemma (o₁ +ℕ o₂) n₂ (c₁ *-nonzero c₂) (∙ᵖ-spine c₁ q) ⟩
  expandˢ (o₁ +ℕ o₂) (K (c₁ *-nonzero c₂)) +ⁱ expandˢ ((o₁ +ℕ o₂) +ℕ ⟅ n₂ ⇓⟆) (∙ᵖ-spine c₁ q)  ≈⟨ +ⁱ-congˡ (expandˢ-≡-cong (Nat.+-assoc o₁ o₂ ⟅ n₂ ⇓⟆)) ⟩
  expandˢ (o₁ +ℕ o₂) (K (c₁ *-nonzero c₂)) +ⁱ expandˢ (o₁ +ℕ (o₂ +ℕ ⟅ n₂ ⇓⟆)) (∙ᵖ-spine c₁ q)  ≈⟨ +ⁱ-cong (expandˢ-*ᵖ-K-lemma o₁ o₂ c₁ c₂) (expandˢ-∙ᵖ-spine-homo o₁ c₁ (o₂ +ℕ ⟅ n₂ ⇓⟆) q) ⟩
  expandˢ o₁ (K c₁) *ⁱ expandˢ o₂ (K c₂) +ⁱ expandˢ o₁ (K c₁) *ⁱ expandˢ (o₂ +ℕ ⟅ n₂ ⇓⟆) q     ≈⟨ ≈ⁱ-sym (*ⁱ-distribˡ-+ⁱ (expandˢ o₁ (K c₁)) (expandˢ o₂ (K c₂)) _) ⟩
  expandˢ o₁ (K c₁) *ⁱ (expandˢ o₂ (K c₂) +ⁱ expandˢ (o₂ +ℕ ⟅ n₂ ⇓⟆) q)                        ≈⟨ *ⁱ-congˡ (≈ⁱ-sym (expandˢ-+x^-lemma o₂ n₂ c₂ q)) ⟩
  expandˢ o₁ (K c₁) *ⁱ expandˢ o₂ (c₂ +x^ n₂ ∙ q)                                              ∎

expand-*ᵖ-spine-homo : ∀ o₁ p o₂ q → expand (*ᵖ-spine o₁ p o₂ q) ≈ⁱ expandˢ o₁ p *ⁱ expandˢ o₂ q
expand-*ᵖ-spine-homo o₁ (K c₁)          o₂ q = expandˢ-∙ᵖ-spine-homo o₁ c₁ o₂ q
expand-*ᵖ-spine-homo o₁ (c₁ +x^ n₁ ∙ p) o₂ (K c₂) = begin⟨ ≈ⁱ-setoid ⟩
  expandˢ (o₁ +ℕ o₂) (∙ᵖ-spine c₂ (c₁ +x^ n₁ ∙ p)) ≈⟨ expandˢ-≡-cong (Nat.+-comm o₁ o₂) ⟩
  expandˢ (o₂ +ℕ o₁) (∙ᵖ-spine c₂ (c₁ +x^ n₁ ∙ p)) ≈⟨ expandˢ-∙ᵖ-spine-homo o₂ c₂ o₁ (c₁ +x^ n₁ ∙ p) ⟩
  expandˢ o₂ (K c₂) *ⁱ expandˢ o₁ (c₁ +x^ n₁ ∙ p)  ≈⟨ *ⁱ-comm _ _ ⟩
  expandˢ o₁ (c₁ +x^ n₁ ∙ p) *ⁱ expandˢ o₂ (K c₂)  ∎
expand-*ᵖ-spine-homo o₁ (c₁ +x^ n₁ ∙ p) o₂ (c₂ +x^ n₂ ∙ q) = begin⟨ ≈ⁱ-setoid ⟩
  expand ( x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) +ᵖ
           c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q +ᵖ
           c₂ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p +ᵖ
           *ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q )
  ≈⟨ expand-+ᵖ-homo
        ( x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) +ᵖ c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q +ᵖ c₂ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p )
        (*ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q)
   ⟩
  expand ( x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) +ᵖ
           c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q +ᵖ
           c₂ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p ) +ⁱ
  expand ( *ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q )
  ≈⟨ +ⁱ-cong (expand-+ᵖ-homo (x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) +ᵖ c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q)
                             (c₂ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p))
             (expand-*ᵖ-spine-homo (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q)
   ⟩
  expand ( x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂)  +ᵖ
           c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q ) +ⁱ
  expandˢ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) (∙ᵖ-spine c₂ p) +ⁱ
  expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p *ⁱ expandˢ (o₂ +ℕ ⟅ n₂ ⇓⟆) q
  ≈⟨ +ⁱ-congʳ (+ⁱ-cong (expand-+ᵖ-homo (x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂))
                                       (c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q))
                       (expandˢ-≡-cong (≡-cong (λ x → x +ℕ ⟅ n₁ ⇓⟆) (Nat.+-comm o₁ o₂))))

   ⟩
  expandˢ (o₁ +ℕ o₂) (K (c₁ *-nonzero c₂)) +ⁱ
  expandˢ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) (∙ᵖ-spine c₁ q) +ⁱ
  expandˢ (o₂ +ℕ o₁ +ℕ ⟅ n₁ ⇓⟆) (∙ᵖ-spine c₂ p) +ⁱ
  expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p *ⁱ expandˢ (o₂ +ℕ ⟅ n₂ ⇓⟆) q
  ≈⟨ +ⁱ-congʳ (+ⁱ-cong (+ⁱ-congˡ {expandˢ (o₁ +ℕ o₂) (K (c₁ *-nonzero c₂))}
                                 (expandˢ-≡-cong {p = ∙ᵖ-spine c₁ q} (Nat.+-assoc o₁ o₂ ⟅ n₂ ⇓⟆)))
                       (expandˢ-≡-cong (Nat.+-assoc o₂ o₁ ⟅ n₁ ⇓⟆)))
   ⟩
  expandˢ (o₁ +ℕ o₂) (K (c₁ *-nonzero c₂)) +ⁱ
  expandˢ (o₁ +ℕ (o₂ +ℕ ⟅ n₂ ⇓⟆)) (∙ᵖ-spine c₁ q) +ⁱ
  expandˢ (o₂ +ℕ (o₁ +ℕ ⟅ n₁ ⇓⟆)) (∙ᵖ-spine c₂ p) +ⁱ
  expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p *ⁱ expandˢ (o₂ +ℕ ⟅ n₂ ⇓⟆) q
  ≈⟨ +ⁱ-congʳ (+ⁱ-cong (+ⁱ-cong (expandˢ-*ᵖ-K-lemma o₁ o₂ c₁ c₂)
                                (expandˢ-∙ᵖ-spine-homo o₁ c₁ (o₂ +ℕ ⟅ n₂ ⇓⟆) q))
                       (expandˢ-∙ᵖ-spine-homo o₂ c₂ (o₁ +ℕ ⟅ n₁ ⇓⟆) p))
   ⟩
  expandˢ o₁ (K c₁) *ⁱ expandˢ o₂ (K c₂) +ⁱ
  expandˢ o₁ (K c₁) *ⁱ expandˢ (o₂ +ℕ ⟅ n₂ ⇓⟆) q +ⁱ
  expandˢ o₂ (K c₂) *ⁱ expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p +ⁱ
  expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p *ⁱ expandˢ (o₂ +ℕ ⟅ n₂ ⇓⟆) q
  ≈⟨ +ⁱ-congʳ {expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p *ⁱ expandˢ (o₂ +ℕ ⟅ n₂ ⇓⟆) q}
              (+ⁱ-congˡ (*ⁱ-comm (expandˢ o₂ (K c₂)) (expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p) ))
   ⟩
  expandˢ o₁ (K c₁) *ⁱ expandˢ o₂ (K c₂) +ⁱ
  expandˢ o₁ (K c₁) *ⁱ expandˢ (o₂ +ℕ ⟅ n₂ ⇓⟆) q +ⁱ
  expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p *ⁱ expandˢ o₂ (K c₂) +ⁱ
  expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p *ⁱ expandˢ (o₂ +ℕ ⟅ n₂ ⇓⟆) q
  ≈⟨ ≈ⁱ-sym (foil (expandˢ o₁ (K c₁)) _ (expandˢ o₂ (K c₂)) _) ⟩
  (expandˢ o₁ (K c₁) +ⁱ expandˢ (o₁ +ℕ ⟅ n₁ ⇓⟆) p) *ⁱ (expandˢ o₂ (K c₂) +ⁱ expandˢ (o₂ +ℕ ⟅ n₂ ⇓⟆) q)
  ≈⟨ *ⁱ-cong (≈ⁱ-sym (expandˢ-+x^-lemma o₁ n₁ c₁ p)) (≈ⁱ-sym (expandˢ-+x^-lemma o₂ n₂ c₂ q)) ⟩
  expandˢ o₁ (c₁ +x^ n₁ ∙ p) *ⁱ expandˢ o₂ (c₂ +x^ n₂ ∙ q) ∎
  where
  foil : ∀ a b c d → (a +ⁱ b) *ⁱ (c +ⁱ d) ≈ⁱ a *ⁱ c +ⁱ a *ⁱ d +ⁱ b *ⁱ c +ⁱ b *ⁱ d
  foil = solve +ⁱ-*ⁱ-almostCommutativeRing

expand-*ᵖ-homo : ∀ p q → expand (p *ᵖ q) ≈ⁱ expand p *ⁱ expand q
expand-*ᵖ-homo 0ᵖ q = *ⁱ-zeroˡ (expand q)
expand-*ᵖ-homo (x^ o₁ ∙ p) 0ᵖ = ≈ⁱ-sym (*ⁱ-zeroʳ (expand (x^ o₁ ∙ p)))
expand-*ᵖ-homo (x^ o₁ ∙ p) (x^ o₂ ∙ q) = expand-*ᵖ-spine-homo o₁ p o₂ q

expand-∙ᵖ-homo : ∀ c p → expand (c ∙ᵖ p) ≈ⁱ proj₁ c ∙ⁱ expand p
expand-∙ᵖ-homo c₁ 0ᵖ = ≈ⁱ-refl
expand-∙ᵖ-homo c₁ (x^ n ∙ p) = loop c₁ n p
  where
  loop : ∀ c n p → expandˢ n (∙ᵖ-spine c p) ≈ⁱ proj₁ c ∙ⁱ expandˢ n p
  loop c₁ zero (K c₂) = ≈ⁱ-refl
  loop c₁ zero (c₂ +x^ n₂ ∙ p) = +≈+ refl (loop c₁ (pred ⟅ n₂ ⇓⟆) p)
  loop c₁ (suc n) p = +≈+ (sym (zeroʳ (proj₁ c₁))) (loop c₁ n p)

expand‿-ᵖ‿homo : ∀ p → expand (-ᵖ p) ≈ⁱ -ⁱ (expand p)
expand‿-ᵖ‿homo = expand-∙ᵖ-homo -1#-nonzero

---- Witness me ----

expand-isRelHomomorphism : IsRelHomomorphism _≈ᵖ_ _≈ⁱ_ expand
expand-isRelHomomorphism = record { cong = expand-cong }

expand-isRingHomomorphism : IsRingHomomorphism +ᵖ-*ᵖ-rawRing +ⁱ-*ⁱ-rawRing expand
expand-isRingHomomorphism = record
  { isRelHomomorphism = expand-isRelHomomorphism
  ; +-homo = expand-+ᵖ-homo
  ; *-homo = expand-*ᵖ-homo
  ; -‿homo = expand‿-ᵖ‿homo
  ; 0#-homo = ≈ⁱ-refl
  ; 1#-homo = ≈ⁱ-refl
  }

expand-isRingMonomorphism : IsRingMonomorphism +ᵖ-*ᵖ-rawRing +ⁱ-*ⁱ-rawRing expand
expand-isRingMonomorphism = record
  { isRingHomomorphism = expand-isRingHomomorphism
  ; injective = expand-injective
  }

open RingConsequences expand-isRingMonomorphism using (R₂-isIntegralDomain→R₁-isIntegralDomain)

+ᵖ-*ᵖ-isIntegralDomain : IsIntegralDomain Polynomial _≈ᵖ_ _+ᵖ_ _*ᵖ_ -ᵖ_ 0ᵖ 1ᵖ
+ᵖ-*ᵖ-isIntegralDomain = R₂-isIntegralDomain→R₁-isIntegralDomain +ⁱ-*ⁱ-isIntegralDomain

+ᵖ-*ᵖ-integralDomain : IntegralDomain (c ⊔ˡ ℓ) (c ⊔ˡ ℓ)
+ᵖ-*ᵖ-integralDomain = record { isIntegralDomain = +ᵖ-*ᵖ-isIntegralDomain }
open IntegralDomain +ᵖ-*ᵖ-integralDomain using () renaming (commutativeRing to +ᵖ-*ᵖ-commutativeRing)
open CommutativeRing +ᵖ-*ᵖ-commutativeRing using () renaming (+-cong to +ᵖ-cong; +-congˡ to +ᵖ-congˡ; +-congʳ to +ᵖ-congʳ; +-identityʳ to +ᵖ-identityʳ; +-assoc to +ᵖ-assoc; +-comm to +ᵖ-comm)
open CommutativeRing +ᵖ-*ᵖ-commutativeRing using () renaming (zeroʳ to *ᵖ-zeroʳ; -‿inverseˡ to -ᵖ‿inverseˡ; -‿inverseʳ to -ᵖ‿inverseʳ; *-comm to *ᵖ-comm; distribʳ to *ᵖ-distribʳ-+ᵖ; distribˡ to *ᵖ-distribˡ-+ᵖ)

+ᵖ-*ᵖ-almostCommutativeRing : AlmostCommutativeRing (c ⊔ˡ ℓ) (c ⊔ˡ ℓ)
+ᵖ-*ᵖ-almostCommutativeRing = fromCommutativeRing +ᵖ-*ᵖ-commutativeRing isZero
  where
  isZero : ∀ x → Maybe (0ᵖ ≈ᵖ x)
  isZero 0ᵖ = just ≈ᵖ-refl
  isZero (x^ _ ∙ _) = nothing


degreeⁱ≡degreeˢ : ∀ n p → degreeⁱ (expandˢ n p) ≡ ⟨ n +ℕ degreeˢ p ⟩
degreeⁱ≡degreeˢ zero (K c) with proj₁ c ≈? 0#
... | yes c≈0 = contradiction c≈0 (proj₂ c)
... | no  _   = ≡-refl
degreeⁱ≡degreeˢ zero (c +x^ (ℕ+ i) ∙ p) rewrite degreeⁱ≡degreeˢ i p = ≡-refl
degreeⁱ≡degreeˢ (suc n) p rewrite degreeⁱ≡degreeˢ n p = ≡-refl

degreeⁱ≡degree : ∀ p → degreeⁱ (expand p) ≡ degree p
degreeⁱ≡degree 0ᵖ = ≡-refl
degreeⁱ≡degree (x^ n ∙ p) = degreeⁱ≡degreeˢ n p

degreeˢ-cong : ∀ {p q} → p ≈ˢ q → degreeˢ p ≡ degreeˢ q
degreeˢ-cong {K c₁} {K c₂} (K≈ c₁≈c₂) = ≡-refl
degreeˢ-cong {c₁ +x^ n ∙ p} {c₂ +x^ n ∙ q} (+≈ c₁≈c₂ ≡-refl p≈q) rewrite degreeˢ-cong p≈q = ≡-refl

degree-cong : ∀ {p q} → p ≈ᵖ q → degree p ≡ degree q
degree-cong {0ᵖ} {0ᵖ} 0ᵖ≈ = ≡-refl
degree-cong {x^ n ∙ p} {x^ n ∙ q} (0ᵖ≉ ≡-refl p≈q) rewrite degreeˢ-cong p≈q = ≡-refl

degreeⁱ-cong : ∀ {p q} → p ≈ⁱ q → degreeⁱ p ≡ degreeⁱ q
degreeⁱ-cong {0ⁱ} {0ⁱ} 0≈0 = ≡-refl
degreeⁱ-cong {0ⁱ} {c₂ +x∙ q} (0≈+ c₂≈0 0≈q) with degreeⁱ q | degreeⁱ-cong 0≈q
... | ⟨ _ ⟩ | ()
... | -∞    | ≡-refl with c₂ ≈? 0#
...   | yes _ = ≡-refl
...   | no c₂≉0 = contradiction c₂≈0 c₂≉0
degreeⁱ-cong {c₁ +x∙ p} {0ⁱ} (+≈0 c₁≈0 0≈p) with degreeⁱ p | degreeⁱ-cong 0≈p
... | ⟨ _ ⟩ | ()
... | -∞    | ≡-refl with c₁ ≈? 0#
...   | yes _   = ≡-refl
...   | no c₁≉0 = contradiction c₁≈0 c₁≉0
degreeⁱ-cong {c₁ +x∙ p} {c₂ +x∙ q} (+≈+ c₁≈c₂ p≈q) with degreeⁱ p | degreeⁱ q | degreeⁱ-cong p≈q
... | ⟨ n ⟩ | ⟨ n ⟩ | ≡-refl = ≡-refl
... | -∞    | -∞    | ≡-refl with c₁ ≈? 0# | c₂ ≈? 0#
...   | yes c₁≈0 | yes c₂≈0 = ≡-refl
...   | yes c₁≈0 | no  c₂≉0 = contradiction (begin⟨ setoid ⟩ c₂ ≈⟨ sym c₁≈c₂ ⟩ c₁ ≈⟨ c₁≈0 ⟩ 0# ∎) c₂≉0
...   | no  c₁≉0 | yes c₂≈0 = contradiction (begin⟨ setoid ⟩ c₁ ≈⟨ c₁≈c₂     ⟩ c₂ ≈⟨ c₂≈0 ⟩ 0# ∎) c₁≉0
...   | no  c₁≉0 | no  c₂≉0 = ≡-refl

module _ where
  open ≤-Reasoning using (begin_; _≤⟨_⟩_) renaming (_≡⟨_⟩_ to _≡≤⟨_⟩_; _∎ to _≤∎)

  degreeⁱ-+ⁱ : ∀ p q → degreeⁱ (p +ⁱ q) ≤ᵈ degreeⁱ p ⊔ᵈ degreeⁱ q
  degreeⁱ-+ⁱ 0ⁱ q = ≤ᵈ-refl
  degreeⁱ-+ⁱ (c₁ +x∙ p) 0ⁱ with degreeⁱ (c₁ +x∙ p)
  ... | -∞ = ≤ᵈ-refl
  ... | ⟨ _ ⟩ = ≤ᵈ-refl
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) with degreeⁱ (p +ⁱ q) | degreeⁱ p | degreeⁱ q | degreeⁱ-+ⁱ p q
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | n     | m     | (-∞≤ _) with c₁ + c₂ ≈? 0#
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | n     | m     | (-∞≤ _) | yes c₁+c₂≈0 = -∞≤ _
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | -∞    | m     | (-∞≤ _) | no  c₁+c₂≉0 with c₁ ≈? 0#
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | -∞    | -∞    | (-∞≤ _) | no  c₁+c₂≉0 | yes c₁≈0 with c₂ ≈? 0#
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | -∞    | -∞    | (-∞≤ _) | no  c₁+c₂≉0 | yes c₁≈0 | yes c₂≈0 = contradiction (begin⟨ setoid ⟩ c₁ + c₂ ≈⟨ +-cong c₁≈0 c₂≈0 ⟩ 0# + 0# ≈⟨ +-identityʳ 0# ⟩ 0# ∎) c₁+c₂≉0
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | -∞    | -∞    | (-∞≤ _) | no  c₁+c₂≉0 | yes c₁≈0 | no  c₂≉0 = ≤ᵈ-refl
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | -∞    | ⟨ m ⟩ | (-∞≤ _) | no  c₁+c₂≉0 | yes c₁≈0 = ⟨ 0≤n ⟩
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | -∞    | -∞    | (-∞≤ _) | no  c₁+c₂≉0 | no  c₁≉0 with c₂ ≈? 0#
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | -∞    | -∞    | (-∞≤ _) | no  c₁+c₂≉0 | no  c₁≉0 | yes c₂≈0 = ≤ᵈ-refl
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | -∞    | -∞    | (-∞≤ _) | no  c₁+c₂≉0 | no  c₁≉0 | no  c₂≉0 = ⟨ ≤-reflexive (⊔-identityʳ (λ x → 0≤n) 0) ⟩
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | -∞    | ⟨ m ⟩ | (-∞≤ _) | no  c₁+c₂≉0 | no  c₁≉0 = ⟨ begin 0 ≤⟨ 0≤n ⟩ suc m ≡≤⟨ ≡-sym (⊔-identityʳ (λ x → 0≤n) (suc m)) ⟩ 0 ⊔ suc m ≤∎ ⟩
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | ⟨ n ⟩ | -∞    | (-∞≤ _) | no  c₁+c₂≉0 with c₂ ≈? 0#
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | ⟨ n ⟩ | -∞    | (-∞≤ _) | no  c₁+c₂≉0 | yes c₂≈0 = ⟨ 0≤n ⟩
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | ⟨ n ⟩ | -∞    | (-∞≤ _) | no  c₁+c₂≉0 | no  c₂≉0 = ⟨ begin 0 ≤⟨ 0≤n ⟩ suc n ≡≤⟨ ≡-sym (⊔-identityˡ (λ x → 0≤n) (suc n)) ⟩ suc n ⊔ 0 ≤∎ ⟩
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | -∞    | ⟨ n ⟩ | ⟨ m ⟩ | (-∞≤ _) | no  c₁+c₂≉0 = ⟨ 0≤n ⟩
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | -∞    | m     | _ with c₁ ≈? 0#
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | -∞    | -∞    | _       | yes c₁≈0 with c₂ ≈? 0#
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | -∞    | -∞    | ()      | yes c₁≈0 | yes c₂≈0
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | -∞    | -∞    | ()      | yes c₁≈0 | no  c₂≉0
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | -∞    | ⟨ m ⟩ | ⟨ r≤m ⟩ | yes c₁≈0 = ⟨ suc-mono-≤ r≤m ⟩
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | -∞    | -∞    | pf      | no  c₁≉0 with c₂ ≈? 0#
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | -∞    | -∞    | ()      | no  c₁≉0 | yes c₂≈0
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | -∞    | -∞    | ()      | no  c₁≉0 | no  c₂≉0
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | -∞    | ⟨ m ⟩ | ⟨ r≤m ⟩ | no  c₁≉0 = ⟨ begin suc r ≤⟨ suc-mono-≤ r≤m ⟩ suc m ≡≤⟨ ≡-sym (⊔-identityʳ (λ x → 0≤n) (suc m)) ⟩ 0 ⊔ suc m ≤∎ ⟩
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | ⟨ n ⟩ | -∞    | ⟨ r≤n ⟩ with c₂ ≈? 0#
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | ⟨ n ⟩ | -∞    | ⟨ r≤n ⟩ | yes c₂≈0 = ⟨ suc-mono-≤ r≤n ⟩
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | ⟨ n ⟩ | -∞    | ⟨ r≤n ⟩ | no  c₂≉0 = ⟨ begin suc r ≤⟨ suc-mono-≤ r≤n ⟩ suc n ≡≤⟨ ≡-sym (⊔-identityˡ (λ x → 0≤n) (suc n)) ⟩ suc n ⊔ 0 ≤∎ ⟩
  degreeⁱ-+ⁱ (c₁ +x∙ p) (c₂ +x∙ q) | ⟨ r ⟩ | ⟨ n ⟩ | ⟨ m ⟩ | ⟨ r≤n⊔m ⟩ = ⟨ begin suc r ≤⟨ suc-mono-≤ r≤n⊔m ⟩ suc (n ⊔ m) ≡≤⟨ +-distribˡ-⊔ 1 n m ⟩ suc n ⊔ suc m ≤∎ ⟩

  -- degreeⁱ-*ⁱ : ∀ p q → degreeⁱ (p *ⁱ q) ≡ degreeⁱ p +ᵈ degreeⁱ q
  -- degreeⁱ-*ⁱ 0ⁱ q = ≡-refl
  -- degreeⁱ-*ⁱ (c₁ +x∙ p) 0ⁱ with degreeⁱ p
  -- ... | ⟨ n ⟩ = ≡-refl
  -- ... | -∞ with c₁ ≈? 0#
  -- ...   | yes _ = ≡-refl
  -- ...   | no  _ = ≡-refl
  -- degreeⁱ-*ⁱ (c₁ +x∙ p) (c₂ +x∙ q) = {!!}
  --   -- lemma : degreeⁱ ((c₁ * c₂) +x∙ (c₁ ∙ⁱ q +ⁱ c₂ ∙ⁱ p +ⁱ x∙ (p *ⁱ q))) ≡ degreeⁱ (c₁ +x∙ p) +ᵈ degreeⁱ (c₂ +x∙ q)
  --   -- lemma = {!!}


degreeᵖ-+ᵖ : ∀ p q → degree (p +ᵖ q) ≤ᵈ degree p ⊔ᵈ degree q
degreeᵖ-+ᵖ p q = begin
  degree (p +ᵖ q)                          ≡ᵈ⟨ ≡-sym (degreeⁱ≡degree (p +ᵖ q)) ⟩
  degreeⁱ (expand (p +ᵖ q))                ≡ᵈ⟨ degreeⁱ-cong (expand-+ᵖ-homo p q) ⟩
  degreeⁱ (expand p +ⁱ expand q)           ≤ᵈ⟨ degreeⁱ-+ⁱ (expand p) (expand q) ⟩
  degreeⁱ (expand p) ⊔ᵈ degreeⁱ (expand q) ≡ᵈ⟨ ≡-cong₂ _⊔ᵈ_ (degreeⁱ≡degree p) (degreeⁱ≡degree q) ⟩
  degree p ⊔ᵈ degree q                     ∎ᵈ
  where
  open ≤ᵈ-Reasoning

∙ᵖ-spine-degreeˢ : ∀ a p → degreeˢ (∙ᵖ-spine a p) ≡ degreeˢ p
∙ᵖ-spine-degreeˢ a (K c) = ≡-refl
∙ᵖ-spine-degreeˢ a (c +x^ n ∙ p) = ≡-cong (λ x → ⟅ n ⇓⟆ +ℕ x) (∙ᵖ-spine-degreeˢ a p)

∙ᵖ-degree : ∀ a p → degree (a ∙ᵖ p) ≡ degree p
∙ᵖ-degree a 0ᵖ = ≡-refl
∙ᵖ-degree a (x^ n ∙ p) = ≡-cong (λ x → ⟨ n +ℕ x ⟩) (∙ᵖ-spine-degreeˢ a p)

open import Relation.Binary using (Antisymmetric)
open import AKS.Nat using (≤-antisym; ≤-total)

≤ᵈ-antisym : Antisymmetric _≡_ _≤ᵈ_
≤ᵈ-antisym (-∞≤ _) (-∞≤ _) = ≡-refl
≤ᵈ-antisym ⟨ x≤y ⟩ ⟨ y≤x ⟩ = ≡-cong ⟨_⟩ (≤-antisym x≤y y≤x)

m≤ᵈn⇒m⊔ᵈn≡n : ∀ {m n} → m ≤ᵈ n → m ⊔ᵈ n ≡ n
m≤ᵈn⇒m⊔ᵈn≡n { -∞}   {n} m≤n = ≡-refl
m≤ᵈn⇒m⊔ᵈn≡n {⟨ m ⟩} {⟨ n ⟩} ⟨ m≤n ⟩ with ≤-total n m
... | inj₁ n≤m = ≡-cong ⟨_⟩ (≤-antisym m≤n n≤m)
... | inj₂ _   = ≡-refl

degreeⁱ[q]≤degreeⁱ[p+ⁱq] : ∀ p q → degreeⁱ p ≤ᵈ degreeⁱ q → degreeⁱ q ≤ᵈ degreeⁱ (p +ⁱ q)
degreeⁱ[q]≤degreeⁱ[p+ⁱq] 0ⁱ q _ = ≤ᵈ-refl
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) 0ⁱ _ = -∞≤ _
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) _ with degreeⁱ q
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) _      | -∞    with c₂ ≈? 0#
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) _      | -∞    | yes c₂≈0 = -∞≤ _
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) _      | -∞    | no  c₂≉0 with degreeⁱ (p +ⁱ q)
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) _      | -∞    | no  c₂≉0 | -∞    with c₁ + c₂ ≈? 0#
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) _      | -∞    | no  c₂≉0 | -∞    | yes c₁+c₂≈0 with degreeⁱ p
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) _      | -∞    | no  c₂≉0 | -∞    | yes c₁+c₂≈0 | -∞    with c₁ ≈? 0#
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) _      | -∞    | no  c₂≉0 | -∞    | yes c₁+c₂≈0 | -∞    | yes c₁≈0 = contradiction TODO c₂≉0
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) _      | -∞    | no  c₂≉0 | -∞    | yes c₁+c₂≈0 | -∞    | no  c₁≉0 = contradiction TODO c₂≉0
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) ⟨ () ⟩ | -∞    | no  c₂≉0 | -∞    | yes c₁+c₂≈0 | ⟨ n ⟩
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) _      | -∞    | no  c₂≉0 | -∞    | no  c₁+c₂≉0 = ≤ᵈ-refl
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) _      | -∞    | no  c₂≉0 | ⟨ r ⟩ = ⟨ 0≤n ⟩
degreeⁱ[q]≤degreeⁱ[p+ⁱq] (c₁ +x∙ p) (c₂ +x∙ q) _      | ⟨ m ⟩ = TODO

degree[q]≤degree[p+ᵖq] : ∀ p q → degree p ≤ᵈ degree q → degree q ≤ᵈ degree (p +ᵖ q)
degree[q]≤degree[p+ᵖq] p q degree[p]≤degree[q] = begin
  degree q                       ≡ᵈ⟨ ≡-sym (degreeⁱ≡degree q) ⟩
  degreeⁱ (expand q)             ≤ᵈ⟨ degreeⁱ[q]≤degreeⁱ[p+ⁱq] (expand p) (expand q) degreeⁱ[p]≤degreeⁱ[q] ⟩
  degreeⁱ (expand p +ⁱ expand q) ≡ᵈ⟨ ≡-sym (degreeⁱ-cong (expand-+ᵖ-homo p q)) ⟩
  degreeⁱ (expand (p +ᵖ q))      ≡ᵈ⟨ degreeⁱ≡degree (p +ᵖ q) ⟩
  degree (p +ᵖ q)                ∎ᵈ
  where
  open ≤ᵈ-Reasoning
  degreeⁱ[p]≤degreeⁱ[q] : degreeⁱ (expand p) ≤ᵈ degreeⁱ (expand q)
  degreeⁱ[p]≤degreeⁱ[q] = begin
    degreeⁱ (expand p) ≡ᵈ⟨ degreeⁱ≡degree p ⟩
    degree p           ≤ᵈ⟨ degree[p]≤degree[q] ⟩
    degree q           ≡ᵈ⟨ ≡-sym (degreeⁱ≡degree q) ⟩
    degreeⁱ (expand q) ∎ᵈ

-- idea : ∀ o₁ p o₂ q → o₁ < o₂ → degree (x^ o₁ ∙ p +ᵖ x^ o₂ ∙ q) ≡ degree (x^ o₂ ∙ q)
-- idea o₁ p o₂ q o₁<o₂ with <-cmp o₁ o₂
-- idea o₁ (K c₁)          o₂ q o₁<o₂ | tri< _ _ _ = {!!}
-- idea o₁ (c₁ +x^ n₁ ∙ p) o₂ q o₁<o₂ | tri< _ _ _ with +ᵖ-spine ⟅ n₁ ⇓⟆ p (o₂ ∸ o₁) q
-- idea o₁ (c₁ +x^ n₁ ∙ p) o₂ q o₁<o₂ | tri< _ _ _ | 0ᵖ = {!!}
-- idea o₁ (c₁ +x^ n₁ ∙ p) o₂ q o₁<o₂ | tri< _ _ _ | x^ zero ∙ r = {!!}
-- idea o₁ (c₁ +x^ n₁ ∙ p) o₂ q o₁<o₂ | tri< _ _ _ | x^ suc n₃ ∙ r = {!!}
-- idea o₁ p o₂ q o₁<o₂ | tri≈ o₁≮o₂ _ _ = contradiction o₁<o₂ o₁≮o₂
-- idea o₁ p o₂ q o₁<o₂ | tri> o₁≮o₂ _ _ = contradiction o₁<o₂ o₁≮o₂

*ᵖ-degree : ∀ p q → degree (p *ᵖ q) ≡ degree p +ᵈ degree q
*ᵖ-degree 0ᵖ q = ≡-refl
*ᵖ-degree (x^ o₁ ∙ p) 0ᵖ = ≡-refl
*ᵖ-degree (x^ o₁ ∙ p) (x^ o₂ ∙ q) = *ᵖ-spine-degree o₁ p o₂ q
  where
  *ᵖ-spine-degree : ∀ o₁ p o₂ q → degree (*ᵖ-spine o₁ p o₂ q) ≡ ⟨ (o₁ +ℕ degreeˢ p) +ℕ (o₂ +ℕ degreeˢ q) ⟩
  *ᵖ-spine-degree o₁ (K c₁) o₂ q = begin⟨ ≡-setoid Degree ⟩
    ⟨ (o₁ +ℕ o₂) +ℕ degreeˢ (∙ᵖ-spine c₁ q) ⟩ ≡⟨ ≡-cong (λ t → ⟨ o₁ +ℕ o₂ +ℕ t ⟩) (∙ᵖ-spine-degreeˢ c₁ q) ⟩
    ⟨ (o₁ +ℕ o₂) +ℕ degreeˢ q ⟩               ≡⟨ ≡-cong ⟨_⟩ (Nat.+-assoc o₁ o₂ (degreeˢ q))  ⟩
    ⟨ o₁ +ℕ (o₂ +ℕ degreeˢ q) ⟩               ≡⟨ ≡-cong (λ t → ⟨ t +ℕ (o₂ +ℕ degreeˢ q) ⟩) (≡-sym (Nat.+-identityʳ o₁)) ⟩
    ⟨ (o₁ +ℕ 0) +ℕ (o₂ +ℕ degreeˢ q) ⟩        ∎
  *ᵖ-spine-degree o₁ (c₁ +x^ n₁ ∙ p) o₂ (K c₂) = begin⟨ ≡-setoid Degree ⟩
    ⟨ o₁ +ℕ o₂ +ℕ (⟅ n₁ ⇓⟆ +ℕ degreeˢ (∙ᵖ-spine c₂ p)) ⟩ ≡⟨ ≡-cong (λ t → ⟨ o₁ +ℕ o₂ +ℕ (⟅ n₁ ⇓⟆ +ℕ t) ⟩) (∙ᵖ-spine-degreeˢ c₂ p) ⟩
    ⟨ o₁ +ℕ o₂ +ℕ (⟅ n₁ ⇓⟆ +ℕ degreeˢ p) ⟩               ≡⟨ ≡-cong ⟨_⟩ (lemma o₁ o₂ ⟅ n₁ ⇓⟆ (degreeˢ p)) ⟩
    ⟨ o₁ +ℕ (⟅ n₁ ⇓⟆ +ℕ degreeˢ p) +ℕ (o₂ +ℕ 0) ⟩        ∎
    where
    lemma : ∀ x y n d → x +ℕ y +ℕ (n +ℕ d) ≡ x +ℕ (n +ℕ d) +ℕ (y +ℕ 0)
    lemma = solve Nat.ring
  *ᵖ-spine-degree o₁ (c₁ +x^ n₁ ∙ p) o₂ (c₂ +x^ n₂ ∙ q) = ≤ᵈ-antisym deg<deg+deg deg+deg<deg
    where
    open ≤ᵈ-Reasoning
    last-larger : degree (x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) +ᵖ c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q +ᵖ c₂ ∙ᵖ (x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p)) ≤ᵈ degree (*ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q)
    last-larger = TODO
    deg<deg+deg : degree (*ᵖ-spine o₁ (c₁ +x^ n₁ ∙ p) o₂ (c₂ +x^ n₂ ∙ q)) ≤ᵈ ⟨ (o₁ +ℕ degreeˢ (c₁ +x^ n₁ ∙ p)) +ℕ (o₂ +ℕ degreeˢ (c₂ +x^ n₂ ∙ q)) ⟩
    deg<deg+deg = begin
      degree
       (x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) +ᵖ c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q +ᵖ
        c₂ ∙ᵖ (x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p) +ᵖ *ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q)
      ≤ᵈ⟨ degreeᵖ-+ᵖ (x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) +ᵖ c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q +ᵖ c₂ ∙ᵖ (x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p))
                     (*ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q)
        ⟩
      degree (x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) +ᵖ c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q +ᵖ c₂ ∙ᵖ (x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p))
      ⊔ᵈ
      degree (*ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q)
      ≡ᵈ⟨ m≤ᵈn⇒m⊔ᵈn≡n last-larger ⟩
      degree (*ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q)
      ≡ᵈ⟨ *ᵖ-spine-degree (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q  ⟩
      ⟨ ((o₁ +ℕ ⟅ n₁ ⇓⟆) +ℕ degreeˢ p) +ℕ ((o₂ +ℕ ⟅ n₂ ⇓⟆) +ℕ degreeˢ q) ⟩
      ≡ᵈ⟨ ≡-cong₂ (λ x y → ⟨ x +ℕ y ⟩) (Nat.+-assoc o₁ ⟅ n₁ ⇓⟆ (degreeˢ p)) (Nat.+-assoc o₂ ⟅ n₂ ⇓⟆ (degreeˢ q)) ⟩
      ⟨ o₁ +ℕ (⟅ n₁ ⇓⟆ +ℕ degreeˢ p) +ℕ (o₂ +ℕ (⟅ n₂ ⇓⟆ +ℕ degreeˢ q))   ⟩ ∎ᵈ

    deg+deg<deg : ⟨ o₁ +ℕ degreeˢ (c₁ +x^ n₁ ∙ p) +ℕ (o₂ +ℕ degreeˢ (c₂ +x^ n₂ ∙ q)) ⟩ ≤ᵈ degree (*ᵖ-spine o₁ (c₁ +x^ n₁ ∙ p) o₂ (c₂ +x^ n₂ ∙ q))
    deg+deg<deg = begin
      ⟨ (o₁ +ℕ (⟅ n₁ ⇓⟆ +ℕ degreeˢ p)) +ℕ (o₂ +ℕ (⟅ n₂ ⇓⟆ +ℕ degreeˢ q)) ⟩
      ≡ᵈ⟨ ≡-cong₂ (λ x y → ⟨ x +ℕ y ⟩) (≡-sym (Nat.+-assoc o₁ ⟅ n₁ ⇓⟆ (degreeˢ p))) (≡-sym (Nat.+-assoc o₂ ⟅ n₂ ⇓⟆ (degreeˢ q))) ⟩
      ⟨ ((o₁ +ℕ ⟅ n₁ ⇓⟆) +ℕ degreeˢ p) +ℕ ((o₂ +ℕ ⟅ n₂ ⇓⟆) +ℕ degreeˢ q) ⟩
      ≡ᵈ⟨ ≡-sym (*ᵖ-spine-degree (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q) ⟩
      degree (*ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q)
        ≤ᵈ⟨ degree[q]≤degree[p+ᵖq] (x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) +ᵖ c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q +ᵖ c₂ ∙ᵖ (x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p)) (*ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q) last-larger  ⟩
      degree (*ᵖ-spine o₁ (c₁ +x^ n₁ ∙ p) o₂ (c₂ +x^ n₂ ∙ q)) ∎ᵈ


-ᵖ-degree : ∀ p → degree (-ᵖ p) ≡ degree p
-ᵖ-degree = ∙ᵖ-degree -1#-nonzero

deg-+ᵖ : ∀ p q {p≉0} {q≉0} {p+q≉0} → deg (p +ᵖ q) {p+q≉0} ≤ deg p {p≉0} ⊔ deg q {q≉0}
deg-+ᵖ 0ᵖ q {p≉0} {q≉0} {p+q≉0} = contradiction ≈ᵖ-refl p≉0
deg-+ᵖ (x^ o₁ ∙ p) 0ᵖ {p≉0} {q≉0} {p+q≉0} = contradiction ≈ᵖ-refl q≉0
deg-+ᵖ (x^ o₁ ∙ p) (x^ o₂ ∙ q) {p≉0} {q≉0} {p+q≉0} = helper (x^ o₁ ∙ p +ᵖ x^ o₂ ∙ q) {p+q≉0} (degreeᵖ-+ᵖ (x^ o₁ ∙ p) (x^ o₂ ∙ q))
  where
  helper : ∀ d {d≉0} {x} → degree d ≤ᵈ ⟨ x ⟩ → deg d {d≉0} ≤ x
  helper 0ᵖ {d≉0} = contradiction ≈ᵖ-refl d≉0
  helper (x^ o₃ ∙ d) {d≉0} ⟨ pf ⟩ = pf

deg-cong : ∀ {p q} {p≉0} {q≉0} → p ≈ᵖ q → deg p {p≉0} ≡ deg q {q≉0}
deg-cong {0ᵖ} {q} {p≉0} {q≉0} p≈q = contradiction ≈ᵖ-refl p≉0
deg-cong {x^ o₁ ∙ p} {0ᵖ} {p≉0} {q≉0} p≈q = contradiction ≈ᵖ-refl q≉0
deg-cong {x^ o₁ ∙ p} {x^ o₂ ∙ q} {p≉0} {q≉0} (0ᵖ≉ ≡-refl p≈q) rewrite degreeˢ-cong p≈q = ≡-refl

data Coefficients : Set (c ⊔ˡ ℓ) where
  0ᶜ : Coefficients
  _∙x^_+_ : C/0 → ℕ → Coefficients → Coefficients

coefficientsˢ : ℕ → Spine → Coefficients → Coefficients
coefficientsˢ o (K c) coeffs = c ∙x^ o + coeffs
coefficientsˢ o (c +x^ n ∙ p) coeffs = coefficientsˢ (o +ℕ ⟅ n ⇓⟆) p (c ∙x^ o + coeffs)

coefficients : Polynomial → Coefficients
coefficients 0ᵖ = 0ᶜ
coefficients (x^ o ∙ p) = coefficientsˢ o p 0ᶜ

polynomial : Coefficients → Polynomial
polynomial 0ᶜ = 0ᵖ
polynomial (c ∙x^ n + p) = c ∙𝑋^ n +ᵖ polynomial p

polynomial∘coefficients≡id : ∀ p → polynomial (coefficients p) ≈ᵖ p
polynomial∘coefficients≡id 0ᵖ = ≈ᵖ-refl
polynomial∘coefficients≡id (x^ o ∙ p) = loop o p 0ᶜ
  where
  lemma : ∀ o c n p → x^ o ∙ K c +ᵖ x^ (o +ℕ ⟅ n ⇓⟆) ∙ p ≈ᵖ x^ o ∙ (c +x^ n ∙ p)
  lemma o c n p = expand-injective $ begin⟨ ≈ⁱ-setoid ⟩
    expand (x^ o ∙ K c +ᵖ x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) ≈⟨ expand-+ᵖ-homo (x^ o ∙ K c) (x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) ⟩
    expandˢ o (K c) +ⁱ expandˢ (o +ℕ ⟅ n ⇓⟆) p  ≈⟨ ≈ⁱ-sym (expandˢ-+x^-lemma o n c p) ⟩
    expandˢ o (c +x^ n ∙ p)                     ∎
  loop : ∀ o p coeffs → polynomial (coefficientsˢ o p coeffs) ≈ᵖ x^ o ∙ p +ᵖ polynomial coeffs
  loop o (K c) coeffs = ≈ᵖ-refl
  loop o (c +x^ n ∙ p) coeffs = begin⟨ ≈ᵖ-setoid ⟩
    polynomial (coefficientsˢ (o +ℕ ⟅ n ⇓⟆) p (c ∙x^ o + coeffs)) ≈⟨ loop (o +ℕ ⟅ n ⇓⟆) p (c ∙x^ o + coeffs) ⟩
    x^ (o +ℕ ⟅ n ⇓⟆) ∙ p +ᵖ (x^ o ∙ K c +ᵖ polynomial coeffs)    ≈⟨ ≈ᵖ-sym (+ᵖ-assoc (x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) (x^ o ∙ K c) (polynomial coeffs)) ⟩
    (x^ (o +ℕ ⟅ n ⇓⟆) ∙ p +ᵖ x^ o ∙ K c) +ᵖ polynomial coeffs    ≈⟨ +ᵖ-congʳ (+ᵖ-comm (x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) (x^ o ∙ K c)) ⟩
    (x^ o ∙ K c +ᵖ x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) +ᵖ polynomial coeffs    ≈⟨ +ᵖ-congʳ {polynomial coeffs} {x^ o ∙ K c +ᵖ x^ (o +ℕ ⟅ n ⇓⟆) ∙ p} {x^ o ∙ (c +x^ n ∙ p)} (lemma _ _ _ _) ⟩
    (x^ o ∙ (c +x^ n ∙ p)) +ᵖ polynomial coeffs                  ∎

coefficientsˢ≢0ᶜ : ∀ o p coeffs → coefficientsˢ o p coeffs ≢ 0ᶜ
coefficientsˢ≢0ᶜ o (K c) coeffs = λ ()
coefficientsˢ≢0ᶜ o (c +x^ n ∙ p) coeffs = coefficientsˢ≢0ᶜ (o +ℕ ⟅ n ⇓⟆) p (c ∙x^ o + coeffs)

coefficients≢0ᶜ : ∀ p {p≉0 : p ≉ᵖ 0ᵖ} → coefficients p ≢ 0ᶜ
coefficients≢0ᶜ 0ᵖ {p≉0} = contradiction ≈ᵖ-refl p≉0
coefficients≢0ᶜ (x^ o ∙ p) {p≉0} = coefficientsˢ≢0ᶜ o p 0ᶜ

degᶜ : ∀ c {c≉0 : c ≢ 0ᶜ} → ℕ
degᶜ 0ᶜ {c≉0} = contradiction ≡-refl c≉0
degᶜ (_ ∙x^ n + _) = n

degᶜ[coefficients] : ∀ p {p≉0} → degᶜ (coefficients p) {coefficients≢0ᶜ p {p≉0}} ≡ deg p {p≉0}
degᶜ[coefficients] 0ᵖ {p≉0} = contradiction ≈ᵖ-refl p≉0
degᶜ[coefficients] (x^ o ∙ p) = loop o p 0ᶜ
  where
  loop : ∀ o p coeffs → degᶜ (coefficientsˢ o p coeffs) {coefficientsˢ≢0ᶜ o p coeffs} ≡ o +ℕ degreeˢ p
  loop o (K c) coeffs = ≡-sym (Nat.+-identityʳ o)
  loop o (c +x^ n ∙ p) coeffs = begin⟨ ≡-setoid ℕ ⟩
    degᶜ (coefficientsˢ (o +ℕ ⟅ n ⇓⟆) p (c ∙x^ o + coeffs)) ≡⟨ loop (o +ℕ ⟅ n ⇓⟆) p (c ∙x^ o + coeffs) ⟩
    (o +ℕ ⟅ n ⇓⟆) +ℕ degreeˢ p                              ≡⟨ Nat.+-assoc o ⟅ n ⇓⟆ (degreeˢ p) ⟩
    o +ℕ (⟅ n ⇓⟆ +ℕ degreeˢ p)                              ∎

-- leading : ∀ p {p≉0 : p ≉ᵖ 0ᵖ} → Leading p {p≉0}
-- leading p {p≉0} = helper (coefficients p) {coefficients≢0ᶜ p {p≉0}} (polynomial∘coefficients≡id p) (degᶜ[coefficients] p)
--   where
--   helper : ∀ coeffs {coeffs≢0} → polynomial coeffs ≈ᵖ p → degᶜ coeffs {coeffs≢0} ≡ deg p {p≉0} → Leading p {p≉0}
--   helper 0ᶜ {coeffs≢0} = contradiction ≡-refl coeffs≢0
--   helper (leading-coefficient ∙x^ leading-degree + next-term) roundtrip leading-degree≡degree =
--     Leading✓ leading-coefficient leading-degree leading-degree≡degree (polynomial next-term) {!!} roundtrip


data Remainder (r : Polynomial) (m : Polynomial) {m≉0 : m ≉ᵖ 0ᵖ} : Set (c ⊔ˡ ℓ) where
  0ᵖ≈ : (r≈0 : r ≈ᵖ 0ᵖ) → Remainder r m
  0ᵖ≉ : (r≉0 : r ≉ᵖ 0ᵖ) → deg r {r≉0} < deg m {m≉0} → Remainder r m

record Leading (p : Polynomial) {p≉0 : p ≉ᵖ 0ᵖ} : Set (c ⊔ˡ ℓ) where
  constructor Leading✓
  field
    leading-coefficent : C/0
    leading-degree : ℕ
    leading-degree≡degree : leading-degree ≡ deg p {p≉0}
    next-term : Polynomial
    next-term<p : Remainder next-term p {p≉0}
    proof : leading-coefficent ∙𝑋^ leading-degree +ᵖ next-term ≈ᵖ p

leading : ∀ p {p≉0 : p ≉ᵖ 0ᵖ} → Leading p {p≉0}
leading 0ᵖ {p≉0} = contradiction ≈ᵖ-refl p≉0
leading (x^ o ∙ p) {p≉0} = loop o p {p≉0}
  where
  open ≤-Reasoning using (begin-strict_; _<⟨_⟩_; _≤⟨_⟩_) renaming (_≡⟨_⟩_ to _≡≤⟨_⟩_; _∎ to _≤∎)
  degree-step : ∀ o n c p → deg (x^ o +ℕ ⟅ n ⇓⟆ ∙ p) {λ ()} ≡ deg (x^ o ∙ (c +x^ n ∙ p)) {λ ()}
  degree-step o n c p = Nat.+-assoc o ⟅ n ⇓⟆ (degreeˢ p)

  remainder-smaller : ∀ o n c p {r≉0} {r'≉0} → deg (x^ o ∙ K c) {r≉0} < deg (x^ o ∙ (c +x^ n ∙ p)) {r'≉0}
  remainder-smaller o (ℕ+ n) c p = lte (n +ℕ degreeˢ p) (lemma o n (degreeˢ p))
    where
    lemma : ∀ x y z → suc (x +ℕ 0 +ℕ (y +ℕ z)) ≡ x +ℕ suc (y +ℕ z)
    lemma = solve Nat.ring

  remainder-base : ∀ next o n c p {r≉0} → next ≈ᵖ 0ᵖ → Remainder ((x^ o ∙ K c) +ᵖ next) (x^ o ∙ (c +x^ n ∙ p)) {r≉0}
  remainder-base next o n c p {r≉0} next≈0 = 0ᵖ≉ c∙𝑋^o+next≉0 smaller
    where
    c∙𝑋^o≈c∙𝑋^o+next : c ∙𝑋^ o ≈ᵖ c ∙𝑋^ o +ᵖ next
    c∙𝑋^o≈c∙𝑋^o+next = begin⟨ ≈ᵖ-setoid ⟩
      c ∙𝑋^ o         ≈⟨ ≈ᵖ-sym (+ᵖ-identityʳ _) ⟩
      c ∙𝑋^ o +ᵖ 0ᵖ   ≈⟨ +ᵖ-congˡ {c ∙𝑋^ o} (≈ᵖ-sym next≈0) ⟩
      c ∙𝑋^ o +ᵖ next ∎
    c∙𝑋^o+next≉0 : c ∙𝑋^ o +ᵖ next ≉ᵖ 0ᵖ
    c∙𝑋^o+next≉0 c∙𝑋^o+next≈0 = contradiction (begin⟨ ≈ᵖ-setoid ⟩ c ∙𝑋^ o ≈⟨ c∙𝑋^o≈c∙𝑋^o+next ⟩ c ∙𝑋^ o +ᵖ next ≈⟨ c∙𝑋^o+next≈0 ⟩ 0ᵖ ∎) (λ ())
    smaller : deg ((x^ o ∙ K c) +ᵖ next) {c∙𝑋^o+next≉0} < deg (x^ o ∙ (c +x^ n ∙ p)) {r≉0}
    smaller = begin-strict
      deg (x^ o ∙ K c +ᵖ next)          ≡≤⟨ deg-cong {p≉0 = c∙𝑋^o+next≉0} {q≉0 = λ ()} (≈ᵖ-sym (c∙𝑋^o≈c∙𝑋^o+next)) ⟩
      deg (x^ o ∙ K c) {λ ()}            <⟨ remainder-smaller o n c p {λ ()} {r≉0} ⟩
      deg (x^ o ∙ (c +x^ n ∙ p)) {r≉0}   ≤∎

  remainder-step : ∀ next o n c p {r≉0} → Remainder next (x^ o +ℕ ⟅ n ⇓⟆ ∙ p) {λ ()} → Remainder ((x^ o ∙ K c) +ᵖ next) (x^ o ∙ (c +x^ n ∙ p)) {r≉0}
  remainder-step next o n c p {r≉0} (0ᵖ≈ next≈0) = remainder-base next o n c p next≈0
  remainder-step next o n c p {r≉0} (0ᵖ≉ next≉0 next<r) with x^ o ∙ K c +ᵖ next ≈ᵖ? 0ᵖ
  ... | yes r'≈0 = 0ᵖ≈ r'≈0
  ... | no  r'≉0 = 0ᵖ≉ r'≉0 smaller
    where
    smaller : deg ((x^ o ∙ K c) +ᵖ next) {r'≉0} < deg (x^ o ∙ (c +x^ n ∙ p)) {r≉0}
    smaller rewrite degree-step o n c p = begin-strict
      deg ((x^ o ∙ K c) +ᵖ next) {r'≉0}           ≤⟨ deg-+ᵖ (x^ o ∙ K c) next {p≉0 = λ ()} ⟩
      deg (x^ o ∙ K c) {λ ()} ⊔ deg next {next≉0} <⟨ ⊔-least-< (deg (x^ o ∙ K c) {λ ()}) (deg next) (deg (x^ o ∙ (c +x^ n ∙ p)) {r≉0}) (remainder-smaller o n c p {λ ()} {r≉0}) next<r ⟩
      deg (x^ o ∙ (c +x^ n ∙ p)) {r≉0}            ≤∎

  lemma : ∀ o c n p → x^ o ∙ K c +ᵖ x^ (o +ℕ ⟅ n ⇓⟆) ∙ p ≈ᵖ x^ o ∙ (c +x^ n ∙ p)
  lemma o c n p = expand-injective $ begin⟨ ≈ⁱ-setoid ⟩
    expand (x^ o ∙ K c +ᵖ x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) ≈⟨ expand-+ᵖ-homo (x^ o ∙ K c) (x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) ⟩
    expandˢ o (K c) +ⁱ expandˢ (o +ℕ ⟅ n ⇓⟆) p  ≈⟨ ≈ⁱ-sym (expandˢ-+x^-lemma o n c p) ⟩
    expandˢ o (c +x^ n ∙ p)                     ∎

  proof-step
    : ∀ lc o n c p next
    → lc ∙𝑋^ deg (x^ o +ℕ ⟅ n ⇓⟆ ∙ p) {λ ()} +ᵖ next ≈ᵖ x^ o +ℕ ⟅ n ⇓⟆ ∙ p
    → lc ∙𝑋^ deg (x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) {λ ()} +ᵖ ((x^ o ∙ K c) +ᵖ next) ≈ᵖ x^ o ∙ (c +x^ n ∙ p)
  proof-step lc o n c p next pf = begin⟨ ≈ᵖ-setoid ⟩
    lc ∙𝑋^ deg (x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) {λ ()} +ᵖ (x^ o ∙ K c +ᵖ next) ≈⟨ +ᵖ-congˡ {lc ∙𝑋^ deg (x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) {λ ()}} (+ᵖ-comm (x^ o ∙ K c) next) ⟩
    lc ∙𝑋^ deg (x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) {λ ()} +ᵖ (next +ᵖ x^ o ∙ K c) ≈⟨ ≈ᵖ-sym (+ᵖ-assoc (lc ∙𝑋^ deg (x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) {λ ()}) next (x^ o ∙ K c)) ⟩
    (lc ∙𝑋^ deg (x^ (o +ℕ ⟅ n ⇓⟆) ∙ p) {λ ()} +ᵖ next) +ᵖ x^ o ∙ K c ≈⟨ +ᵖ-congʳ {x^ o ∙ K c} pf ⟩
    x^ o +ℕ ⟅ n ⇓⟆ ∙ p +ᵖ x^ o ∙ K c                                  ≈⟨ +ᵖ-comm (x^ o +ℕ ⟅ n ⇓⟆ ∙ p) (x^ o ∙ K c) ⟩
    x^ o ∙ K c +ᵖ x^ o +ℕ ⟅ n ⇓⟆ ∙ p                                  ≈⟨ lemma o c n p ⟩
    x^ o ∙ (c +x^ n ∙ p)                                              ∎

  loop : ∀ o p {p≉0 : x^ o ∙ p ≉ᵖ 0ᵖ} → Leading (x^ o ∙ p) {p≉0}
  loop o (K c) = Leading✓ c o (≡-sym (Nat.+-identityʳ o)) 0ᵖ (0ᵖ≈ ≈ᵖ-refl) (+ᵖ-identityʳ (c ∙𝑋^ o))
  loop o (c +x^ n ∙ p) with loop (o +ℕ ⟅ n ⇓⟆) p {λ ()}
  ... | Leading✓ lc d ≡-refl next next<p pf = Leading✓ lc d (degree-step o n c p) (c ∙𝑋^ o +ᵖ next) (remainder-step next o n c p next<p) (proof-step lc o n c p next pf)

record Euclidean (n : Polynomial) (m : Polynomial) {m≉0 : m ≉ᵖ 0ᵖ} : Set (c ⊔ˡ ℓ) where
  constructor Euclidean✓
  field
    q : Polynomial
    r : Polynomial
    division : n ≈ᵖ m *ᵖ q +ᵖ r
    remainder : Remainder r m {m≉0}

divMod-base₁ : ∀ n m → n ≈ᵖ 0ᵖ → n ≈ᵖ m *ᵖ 0ᵖ +ᵖ 0ᵖ
divMod-base₁ n m n≈0 = begin⟨ ≈ᵖ-setoid ⟩
  n ≈⟨ n≈0 ⟩ 0ᵖ ≈⟨ ≈ᵖ-sym (*ᵖ-zeroʳ m) ⟩
  m *ᵖ 0ᵖ       ≈⟨ ≈ᵖ-sym (+ᵖ-identityʳ _) ⟩
  m *ᵖ 0ᵖ +ᵖ 0ᵖ ∎

-- open import Strict using (force)
open import Agda.Builtin.Strict using (primForce; primForceLemma)

force : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (∀ y → x ≡ y → B y) → B x
force {B = B} x f = primForce ≡-refl (primForce {B = λ y → x ≡ y → B y} x f)

force-≡ : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) (f : ∀ y → x ≡ y → B y) → force x f ≡ f x ≡-refl
force-≡ {B = B} x f rewrite primForceLemma {B = λ y → x ≡ y → B y} x f = ≡-refl

divMod : ∀ n m {m≉0} → Euclidean n m {m≉0}
divMod n m {m≉0} with n ≈ᵖ? 0ᵖ
... | yes n≈0 = Euclidean✓ 0ᵖ 0ᵖ (divMod-base₁ n m n≈0) (0ᵖ≈ ≈ᵖ-refl)
... | no  n≉0 = loop 0ᵖ n {n≉0} (solveOver (n ∷ m ∷ []) +ᵖ-*ᵖ-almostCommutativeRing) <-well-founded
  where
  open ≤-Reasoning using (begin-strict_; _<⟨_⟩_; _≤⟨_⟩_) renaming (_≡⟨_⟩_ to _≡≤⟨_⟩_; _∎ to _≤∎)

  term : ∀ r {r≉0} → Polynomial
  term r {r≉0} with leading r {r≉0} | leading m {m≉0}
  ... | Leading✓ lcʳ degʳ _ _ _ _ | Leading✓ lcᵐ degᵐ _ _ _ _ = (lcʳ /-nonzero lcᵐ) ∙𝑋^ (degʳ ∸ degᵐ)

  term-smaller : ∀ r {r≉0 : r ≉ᵖ 0ᵖ} {r'≉0 : r -ᵖ term r {r≉0} *ᵖ m ≉ᵖ 0ᵖ} → deg m {m≉0} ≤ deg r {r≉0} → deg (r -ᵖ term r {r≉0} *ᵖ m) {r'≉0} < deg r {r≉0}
  term-smaller r {r≉0} {r'≉0} m≤r with leading r {r≉0} | leading m {m≉0}
  ... | Leading✓ lcʳ degʳ degʳ-pf restʳ restʳ<r pfʳ | Leading✓ lcᵐ degᵐ ≡-refl degᵐ-pf restᵐ<m pfᵐ = begin-strict
    deg (r -ᵖ ((lcʳ /-nonzero lcᵐ) ∙𝑋^ (degʳ ∸ degᵐ)) *ᵖ m) {r'≉0} <⟨ {!!} ⟩
    deg r {r≉0}                                                    ≤∎
  -- restʳ -ᵖ (lcʳ /-nonzero lcᵐ) ∙𝑋^ (degʳ ∸ degᵐ) *ᵖ restᵐ)
  -- deg[r] ∸ deg[m] + deg[restᵐ] < deg[r]

  divMod-base₂ : ∀ q r {r≉0} → n ≈ᵖ m *ᵖ q +ᵖ r → r -ᵖ term r {r≉0} *ᵖ m ≈ᵖ 0ᵖ → n ≈ᵖ m *ᵖ (q +ᵖ term r {r≉0}) +ᵖ 0ᵖ
  divMod-base₂ q r {r≉0} n≈mq+r r-t*m≈0 = begin⟨ ≈ᵖ-setoid ⟩
    n                                                              ≈⟨ n≈mq+r ⟩
    m *ᵖ q +ᵖ r                                                    ≈⟨ ≈ᵖ-sym (+ᵖ-identityʳ _) ⟩
    m *ᵖ q +ᵖ r +ᵖ 0ᵖ                                              ≈⟨ +ᵖ-congˡ {m *ᵖ q +ᵖ r} (≈ᵖ-sym (-ᵖ‿inverseˡ (term r {r≉0} *ᵖ m))) ⟩
    m *ᵖ q +ᵖ r +ᵖ ((-ᵖ (term r {r≉0} *ᵖ m)) +ᵖ term r {r≉0} *ᵖ m) ≈⟨ ≈ᵖ-sym (+ᵖ-assoc (m *ᵖ q +ᵖ r) (-ᵖ (term r *ᵖ m)) (term r *ᵖ m)) ⟩
    ((m *ᵖ q +ᵖ r) -ᵖ term r {r≉0} *ᵖ m) +ᵖ term r {r≉0} *ᵖ m      ≈⟨ +ᵖ-cong (+ᵖ-assoc (m *ᵖ q) r (-ᵖ (term r *ᵖ m))) (*ᵖ-comm (term r) m) ⟩
    (m *ᵖ q +ᵖ (r -ᵖ term r {r≉0} *ᵖ m)) +ᵖ m *ᵖ term r {r≉0}      ≈⟨ +ᵖ-congʳ {m *ᵖ term r} (+ᵖ-congˡ {m *ᵖ q} r-t*m≈0) ⟩
    (m *ᵖ q +ᵖ 0ᵖ) +ᵖ m *ᵖ term r {r≉0}                            ≈⟨ +ᵖ-congʳ {m *ᵖ term r} (+ᵖ-identityʳ (m *ᵖ q)) ⟩
    m *ᵖ q +ᵖ m *ᵖ term r {r≉0}                                    ≈⟨ ≈ᵖ-sym (*ᵖ-distribˡ-+ᵖ m q (term r)) ⟩
    m *ᵖ (q +ᵖ term r {r≉0})                                       ≈⟨ ≈ᵖ-sym (+ᵖ-identityʳ (m *ᵖ (q +ᵖ term r))) ⟩
    m *ᵖ (q +ᵖ term r {r≉0}) +ᵖ 0ᵖ                                 ∎

  divMod-step : ∀ q r {r≉0} → n ≈ᵖ m *ᵖ q +ᵖ r → n ≈ᵖ m *ᵖ (q +ᵖ term r {r≉0}) +ᵖ (r -ᵖ term r {r≉0} *ᵖ m)
  divMod-step q r {r≉0} n≈mq+r = begin⟨ ≈ᵖ-setoid ⟩
    n                                                       ≈⟨ n≈mq+r ⟩
    m *ᵖ q +ᵖ r                                             ≈⟨ ≈ᵖ-sym (+ᵖ-identityʳ _) ⟩
    m *ᵖ q +ᵖ r +ᵖ 0ᵖ                                       ≈⟨ +ᵖ-congˡ {m *ᵖ q +ᵖ r} (≈ᵖ-sym (-ᵖ‿inverseʳ (term r {r≉0} *ᵖ m))) ⟩
    m *ᵖ q +ᵖ r +ᵖ (term r {r≉0} *ᵖ m -ᵖ term r {r≉0} *ᵖ m) ≈⟨ final m q r (term r) (-ᵖ (term r *ᵖ m)) ⟩
    m *ᵖ (q +ᵖ term r {r≉0}) +ᵖ (r -ᵖ term r {r≉0} *ᵖ m)    ∎
    where
    final : ∀ m q r x y → m *ᵖ q +ᵖ r +ᵖ (x *ᵖ m +ᵖ y) ≈ᵖ m *ᵖ (q +ᵖ x) +ᵖ (r +ᵖ y)
    final = solve +ᵖ-*ᵖ-almostCommutativeRing

  loop : ∀ q r {r≉0} → n ≈ᵖ m *ᵖ q +ᵖ r → Acc _<_ (deg r {r≉0}) → Euclidean n m {m≉0}
  loop q r {r≉0} n≈mq+r (acc downward) with <-≤-connex (deg r {r≉0}) (deg m {m≉0})
  ... | inj₁ r<m = Euclidean✓ q r n≈mq+r (0ᵖ≉ r≉0 r<m)
  ... | inj₂ r≥m with (r -ᵖ term r {r≉0} *ᵖ m) ≈ᵖ? 0ᵖ
  ...   | yes r'≈0 = Euclidean✓ (q +ᵖ term r {r≉0}) 0ᵖ (divMod-base₂ q r {r≉0} n≈mq+r r'≈0) (0ᵖ≈ ≈ᵖ-refl)
  ...   | no  r'≉0 = force (q +ᵖ term r {r≉0}) λ { q' ≡-refl → loop q' (r -ᵖ term r {r≉0} *ᵖ m) {r'≉0} (divMod-step q r {r≉0} n≈mq+r) (downward _ (term-smaller r r≥m)) }

-- factor : ∀ p a → ⟦ p ⟧ a ≈ 0# → (𝑋 -ᵖ 𝐾 a) ∣ p
-- factor = TODO
