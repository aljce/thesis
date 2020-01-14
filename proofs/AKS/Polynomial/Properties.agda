open import Level using () renaming (_⊔_ to _⊔ˡ_)
open import Function using (_$_)

open import Function.Equivalence as FE using ()
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Setoid; IsEquivalence; Decidable; Tri)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; cong to ≡-cong; setoid to ≡-setoid)
open Tri

open import Data.Maybe using (nothing)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (inj₁; inj₂)

open import Algebra.Bundles using (CommutativeRing)
open import AKS.Algebra.Bundles using (DecField)

module AKS.Polynomial.Properties {c ℓ} (F : DecField c ℓ) where

open import AKS.Nat using (ℕ; zero; suc; _<_; _≟_; _≟⁺_; _∸_; ℕ⁺; ⟅_⇓⟆; ⟅_⇑⟆) renaming (_+_ to _+ℕ_)
open import AKS.Nat using (<-cmp; <-≤-connex; m+[n∸m]≡n; ℕ→ℕ⁺→ℕ; m<n⇒n∸m≢0; ≢⇒¬≟; <⇒≤)
open import AKS.Nat using (Acc; acc; <-well-founded)

open import Polynomial.Simple.AlmostCommutativeRing using (AlmostCommutativeRing; fromCommutativeRing)
open import Polynomial.Simple.Reflection using (solve; solveOver)

open DecField F
  using (0#; 1#; _+_; _*_; -_; _-_; _⁻¹; _/_)
  renaming (Carrier to C)
open DecField F
  using (C/0; _*-nonzero_; _/-nonzero_; -1#-nonzero; 0#≉1#; *-cancelˡ)
open DecField F using (_≈_; _≉_; _≈?_; setoid)
open Setoid setoid using (refl; sym; trans)
open import Relation.Binary.Reasoning.MultiSetoid
open DecField F using (ring; commutativeRing; *-commutativeMonoid)
open CommutativeRing commutativeRing using (+-assoc; +-comm; +-cong; +-congˡ; +-congʳ; +-identityˡ; +-identityʳ; distribˡ; distribʳ; -‿cong; -‿inverseˡ)
open CommutativeRing commutativeRing using (*-assoc; *-comm; *-cong; *-congˡ; *-congʳ; *-identityˡ; *-identityʳ; zeroˡ; zeroʳ)
open import Algebra.Properties.Ring ring using (-‿distribˡ-*)
open import AKS.Exponentiation *-commutativeMonoid using (_^_; _^⁺_; ^-homo; ^-^⁺-homo; x^n≈x^⁺n)

open import AKS.Polynomial.Base F using
  ( Spine; K; _+x^_∙_; Polynomial; 0ᵖ; x^_∙_; ⟦_⟧; ⟦_⟧ˢ; _+?_; _∙𝑋^_; deg
  ; 1ᵖ; _+ᵖ_; +ᵖ-spine; +ᵖ-spine-≡-K; +ᵖ-spine-≡; +ᵖ-spine-<; -ᵖ_; _-ᵖ_; _*ᵖ_; *ᵖ-spine; _∙ᵖ_; ∙ᵖ-spine
  ; _≈ᵖ_; _≉ᵖ_; ≈✓; _≈ⁱ_; 0ᵖ≈; 0ᵖ≉; _≈ˢ_; K≈; +≈
  ; ≈ⁱ-refl; ≈ⁱ-sym; ≈ⁱ-trans; ≈ᵖ-refl; ≈ᵖ-sym; ≈ᵖ-trans
  )

open import Algebra.Structures {A = Polynomial} _≈ᵖ_ using (IsCommutativeRing; IsRing; IsAbelianGroup; IsGroup; IsMonoid; IsSemigroup; IsMagma)
open import Algebra.Definitions {A = Polynomial} _≈ᵖ_ using
  ( _DistributesOver_; _DistributesOverʳ_; _DistributesOverˡ_
  ; RightIdentity; LeftIdentity; Identity; Associative; Commutative
  ; RightInverse; LeftInverse; Inverse; Congruent₂; Congruent₁
  )
open import AKS.Algebra.Structures Polynomial _≈ᵖ_ using (IsNonZeroCommutativeRing; IsIntegralDomain)

ACR : AlmostCommutativeRing c ℓ
ACR = fromCommutativeRing commutativeRing (λ _ → nothing)

foil : ∀ a b c d → (a + b) * (c + d) ≈ a * c + a * d + b * c + b * d
foil = solve ACR

≈ⁱ-isEquivalence : IsEquivalence _≈ⁱ_
≈ⁱ-isEquivalence = record
  { refl = ≈ⁱ-refl
  ; sym = ≈ⁱ-sym
  ; trans = ≈ⁱ-trans
  }

≈ⁱ-setoid : Setoid (c ⊔ˡ ℓ) (c ⊔ˡ ℓ)
≈ⁱ-setoid = record
  { Carrier = Polynomial
  ; _≈_ = _≈ⁱ_
  ; isEquivalence = ≈ⁱ-isEquivalence
  }

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

_≈ⁱ?_ : Decidable _≈ⁱ_
0ᵖ ≈ⁱ? 0ᵖ = yes ≈ⁱ-refl
0ᵖ ≈ⁱ? (x^ m ∙ q) = no λ ()
(x^ n ∙ p) ≈ⁱ? 0ᵖ = no λ ()
(x^ n ∙ p) ≈ⁱ? (x^ m ∙ q) with n ≟ m
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

≈ᵖ-setoid : Setoid (c ⊔ˡ ℓ) (c ⊔ˡ ℓ)
≈ᵖ-setoid = record
  { Carrier = Polynomial
  ; _≈_ = _≈ᵖ_
  ; isEquivalence = ≈ᵖ-isEquivalence
  }

≈ⁱ⇒≈ᵖ : ∀ {p q} → p ≈ⁱ q → p ≈ᵖ q
≈ⁱ⇒≈ᵖ {0ᵖ} {0ᵖ} 0ᵖ≈ = ≈ᵖ-refl
≈ⁱ⇒≈ᵖ {x^ n ∙ p} {x^ n ∙ q} (0ᵖ≉ ≡-refl p≈ˢq) = ≈✓ λ x → *-congˡ (≈ˢ⇒∀x[pₓ≈qₓ] p q p≈ˢq x)
  where
  ≈ˢ⇒∀x[pₓ≈qₓ] : ∀ p q → p ≈ˢ q → ∀ x → ⟦ p ⟧ˢ x ≈ ⟦ q ⟧ˢ x
  ≈ˢ⇒∀x[pₓ≈qₓ] (K c₁) (K c₂) (K≈ c₁≈c₂) x = c₁≈c₂
  ≈ˢ⇒∀x[pₓ≈qₓ] (c₁ +x^ n ∙ p) (c₂ +x^ n ∙ q) (+≈ c₁≈c₂ ≡-refl p≈ˢq) x = begin⟨ setoid ⟩
    proj₁ c₁ + x ^⁺ n * ⟦ p ⟧ˢ x ≈⟨ +-cong c₁≈c₂ (*-congˡ (≈ˢ⇒∀x[pₓ≈qₓ] p q p≈ˢq x)) ⟩
    proj₁ c₂ + x ^⁺ n * ⟦ q ⟧ˢ x ∎

1ᵖ-homo : ∀ x → ⟦ 1ᵖ ⟧ x ≈ 1#
1ᵖ-homo x = begin⟨ setoid ⟩
  1# * 1# ≈⟨ *-identityʳ 1# ⟩ 1# ∎

+ᵖ-spine-≡-K-homo : ∀ n c p x → ⟦ +ᵖ-spine-≡-K n c p ⟧ x ≈ x ^ n * (proj₁ c + ⟦ p ⟧ˢ x)
+ᵖ-spine-≡-K-homo n c₁ (K c₂) x with proj₁ c₁ + proj₁ c₂ ≈? 0#
... | yes c₁+c₂≈0 = begin⟨ setoid ⟩
  0#                            ≈⟨ sym (zeroʳ (x ^ n)) ⟩
  x ^ n * 0#                    ≈⟨ *-congˡ (sym c₁+c₂≈0) ⟩
  x ^ n * (proj₁ c₁ + proj₁ c₂) ∎
... | no  c₁+c₂≉0 = refl
+ᵖ-spine-≡-K-homo n c₁ (c₂ +x^ i₂ ∙ p) x with proj₁ c₁ + proj₁ c₂ ≈? 0#
... | yes c₁+c₂≈0 = begin⟨ setoid ⟩
  x ^ (n +ℕ ⟅ i₂ ⇓⟆) * ⟦ p ⟧ˢ x                       ≈⟨ *-congʳ (^-^⁺-homo x n i₂) ⟩
  (x ^ n * x ^⁺ i₂) * ⟦ p ⟧ˢ x                         ≈⟨ *-assoc (x ^ n) (x ^⁺ i₂) (⟦ p ⟧ˢ x) ⟩
  x ^ n * (x ^⁺ i₂ * ⟦ p ⟧ˢ x)                         ≈⟨ *-congˡ (sym (+-identityˡ (x ^⁺ i₂ * ⟦ p ⟧ˢ x))) ⟩
  x ^ n * (0# + x ^⁺ i₂ * ⟦ p ⟧ˢ x)                    ≈⟨ *-congˡ (+-congʳ (sym c₁+c₂≈0)) ⟩
  x ^ n * ((proj₁ c₁ + proj₁ c₂) + x ^⁺ i₂ * ⟦ p ⟧ˢ x) ≈⟨ *-congˡ (+-assoc (proj₁ c₁) (proj₁ c₂) (x ^⁺ i₂ * ⟦ p ⟧ˢ x)) ⟩
  x ^ n * (proj₁ c₁ + (proj₁ c₂ + x ^⁺ i₂ * ⟦ p ⟧ˢ x)) ∎
... | no  c₁+c₂≉0 = begin⟨ setoid ⟩
  x ^ n * ((proj₁ c₁ + proj₁ c₂) + x ^⁺ i₂ * ⟦ p ⟧ˢ x) ≈⟨ *-congˡ (+-assoc (proj₁ c₁) (proj₁ c₂) (x ^⁺ i₂ * ⟦ p ⟧ˢ x)) ⟩
  x ^ n * (proj₁ c₁ + (proj₁ c₂ + x ^⁺ i₂ * ⟦ p ⟧ˢ x)) ∎


+ᵖ-spine-≡-homo : ∀ n p q x → ⟦ +ᵖ-spine-≡ n p q ⟧ x ≈ x ^ n * ⟦ p ⟧ˢ x + x ^ n * ⟦ q ⟧ˢ x
+ᵖ-spine-<-homo : ∀ n₁ p n₂ q n₁<n₂ x → ⟦ +ᵖ-spine-< n₁ p n₂ q n₁<n₂ ⟧ x ≈ x ^ n₁ * ⟦ p ⟧ˢ x + x ^ n₂ * ⟦ q ⟧ˢ x
+ᵖ-spine-homo : ∀ n₁ p n₂ q x → ⟦ +ᵖ-spine n₁ p n₂ q ⟧ x ≈ x ^ n₁ * ⟦ p ⟧ˢ x + x ^ n₂ * ⟦ q ⟧ˢ x

+ᵖ-spine-≡-lemma₁ : ∀ x a b p q → x * p + x * q + x * (a + b) ≈ x * (a + p) + x * (b + q)
+ᵖ-spine-≡-lemma₁ = solve ACR

+ᵖ-spine-≡-lemma₂ : ∀ x a b p q → x * a + x * b + x * (p + q) ≈ x * (a + p) + x * (b + q)
+ᵖ-spine-≡-lemma₂ = solve ACR

+ᵖ-spine-≡-homo n (K c₁) q x = begin⟨ setoid ⟩
  ⟦ +ᵖ-spine-≡-K n c₁ q ⟧ x             ≈⟨ +ᵖ-spine-≡-K-homo n c₁ q x ⟩
  x ^ n * (proj₁ c₁ + ⟦ q ⟧ˢ x)         ≈⟨ distribˡ _ _ _ ⟩
  x ^ n * proj₁ c₁ + (x ^ n) * ⟦ q ⟧ˢ x ∎
+ᵖ-spine-≡-homo n (c₁ +x^ i₁ ∙ p) (K c₂) x = begin⟨ setoid ⟩
  ⟦ +ᵖ-spine-≡-K n c₂ (c₁ +x^ i₁ ∙ p) ⟧ x         ≈⟨ +ᵖ-spine-≡-K-homo n c₂ (c₁ +x^ i₁ ∙ p) x  ⟩
  x ^ n * (proj₁ c₂ + ⟦ c₁ +x^ i₁ ∙ p ⟧ˢ x)       ≈⟨ *-congˡ (+-comm _ _) ⟩
  x ^ n * (⟦ c₁ +x^ i₁ ∙ p ⟧ˢ x + proj₁ c₂)       ≈⟨ distribˡ _ _ _ ⟩
  x ^ n * ⟦ c₁ +x^ i₁ ∙ p ⟧ˢ x + x ^ n * proj₁ c₂ ∎
+ᵖ-spine-≡-homo n (c₁ +x^ i₁ ∙ p) (c₂ +x^ i₂ ∙ q) x with proj₁ c₁ + proj₁ c₂ ≈? 0#
... | yes c₁+c₂≈0 = begin⟨ setoid ⟩
  ⟦ +ᵖ-spine (n +ℕ ⟅ i₁ ⇓⟆) p (n +ℕ ⟅ i₂ ⇓⟆) q ⟧ x                                           ≈⟨ +ᵖ-spine-homo (n +ℕ ⟅ i₁ ⇓⟆) p (n +ℕ ⟅ i₂ ⇓⟆) q x ⟩
  x ^ (n +ℕ ⟅ i₁ ⇓⟆) * ⟦ p ⟧ˢ x + x ^ (n +ℕ ⟅ i₂ ⇓⟆) * ⟦ q ⟧ˢ x                              ≈⟨ sym (+-identityʳ _) ⟩
  x ^ (n +ℕ ⟅ i₁ ⇓⟆) * ⟦ p ⟧ˢ x + x ^ (n +ℕ ⟅ i₂ ⇓⟆) * ⟦ q ⟧ˢ x + 0#                         ≈⟨ +-cong (+-cong (*-congʳ (^-^⁺-homo x n i₁)) (*-congʳ (^-^⁺-homo x n i₂))) (sym (zeroʳ _)) ⟩
  x ^ n * x ^⁺ i₁ * ⟦ p ⟧ˢ x + x ^ n * x ^⁺ i₂ * ⟦ q ⟧ˢ x + x ^ n * 0#                        ≈⟨ +-cong (+-cong (*-assoc _ _ _) (*-assoc _ _ _)) (*-congˡ (sym c₁+c₂≈0)) ⟩
  x ^ n * (x ^⁺ i₁ * ⟦ p ⟧ˢ x) + x ^ n * (x ^⁺ i₂ * ⟦ q ⟧ˢ x) + x ^ n * (proj₁ c₁ + proj₁ c₂) ≈⟨ +ᵖ-spine-≡-lemma₁ _ _ _ _ _ ⟩
  x ^ n * (proj₁ c₁ + x ^⁺ i₁ * ⟦ p ⟧ˢ x) + x ^ n * (proj₁ c₂ + x ^⁺ i₂ * ⟦ q ⟧ˢ x)           ∎
... | no  c₁+c₂≉0 with +ᵖ-spine ⟅ i₁ ⇓⟆ p ⟅ i₂ ⇓⟆ q | +ᵖ-spine-homo ⟅ i₁ ⇓⟆ p ⟅ i₂ ⇓⟆ q x
...   | 0ᵖ | 0≈x^i₁*p+x^i₂*q = begin⟨ setoid ⟩
  x ^ n * (proj₁ c₁ + proj₁ c₂)                                                                   ≈⟨ sym (+-identityʳ _) ⟩
  x ^ n * (proj₁ c₁ + proj₁ c₂) + 0#                                                              ≈⟨ +-cong (distribˡ _ _ _) (sym (zeroʳ _)) ⟩
  x ^ n * proj₁ c₁ + x ^ n * proj₁ c₂ + x ^ n * 0#                                                ≈⟨ +-congˡ (*-congˡ 0≈x^i₁*p+x^i₂*q) ⟩
  x ^ n * proj₁ c₁ + x ^ n * proj₁ c₂ + x ^ n * (x ^ ⟅ i₁ ⇓⟆ * ⟦ p ⟧ˢ x + x ^ ⟅ i₂ ⇓⟆ * ⟦ q ⟧ˢ x) ≈⟨ +-congˡ (*-congˡ (+-cong (*-congʳ (x^n≈x^⁺n x i₁)) (*-congʳ (x^n≈x^⁺n x i₂)))) ⟩
  x ^ n * proj₁ c₁ + x ^ n * proj₁ c₂ + x ^ n * (x ^⁺ i₁ * ⟦ p ⟧ˢ x + x ^⁺ i₂ * ⟦ q ⟧ˢ x)          ≈⟨ +ᵖ-spine-≡-lemma₂ _ _ _ _ _ ⟩
  x ^ n * (proj₁ c₁ + x ^⁺ i₁ * ⟦ p ⟧ˢ x) + x ^ n * (proj₁ c₂ + x ^⁺ i₂ * ⟦ q ⟧ˢ x)                ∎
...   | x^ zero ∙ r   | x^0*r≈x^i₁*p+x^i₂*q = begin⟨ setoid ⟩
  ⟦ +ᵖ-spine-≡-K n (proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0) r ⟧ x                                          ≈⟨ +ᵖ-spine-≡-K-homo n (proj₁ c₁ + proj₁ c₂ , c₁+c₂≉0) r x ⟩
  x ^ n * ((proj₁ c₁ + proj₁ c₂) + ⟦ r ⟧ˢ x)                                                      ≈⟨ distribˡ _ _ _ ⟩
  x ^ n * (proj₁ c₁ + proj₁ c₂) + x ^ n * ⟦ r ⟧ˢ x                                                ≈⟨ +-cong (distribˡ _ _ _) (*-congˡ (sym (*-identityˡ _))) ⟩
  x ^ n * proj₁ c₁ + x ^ n * proj₁ c₂ + x ^ n * (x ^ zero * ⟦ r ⟧ˢ x)                             ≈⟨ +-congˡ (*-congˡ x^0*r≈x^i₁*p+x^i₂*q) ⟩
  x ^ n * proj₁ c₁ + x ^ n * proj₁ c₂ + x ^ n * (x ^ ⟅ i₁ ⇓⟆ * ⟦ p ⟧ˢ x + x ^ ⟅ i₂ ⇓⟆ * ⟦ q ⟧ˢ x) ≈⟨ +-congˡ (*-congˡ (+-cong (*-congʳ (x^n≈x^⁺n x i₁)) (*-congʳ (x^n≈x^⁺n x i₂)))) ⟩
  x ^ n * proj₁ c₁ + x ^ n * proj₁ c₂ + x ^ n * (x ^⁺ i₁ * ⟦ p ⟧ˢ x + x ^⁺ i₂ * ⟦ q ⟧ˢ x)          ≈⟨ +ᵖ-spine-≡-lemma₂ _ _ _ _ _ ⟩
  x ^ n * (proj₁ c₁ + x ^⁺ i₁ * ⟦ p ⟧ˢ x) + x ^ n * (proj₁ c₂ + x ^⁺ i₂ * ⟦ q ⟧ˢ x)                ∎
...   | x^ suc n₃ ∙ r | x^n₃*r≈x^i₁*p+x^i₂*q = begin⟨ setoid ⟩
  x ^ n * (proj₁ c₁ + proj₁ c₂ + x ^⁺ ⟅ suc n₃ ⇑⟆ * ⟦ r ⟧ˢ x)                                     ≈⟨ distribˡ _ _ _ ⟩
  x ^ n * (proj₁ c₁ + proj₁ c₂) + x ^ n * (x ^⁺ ⟅ suc n₃ ⇑⟆ * ⟦ r ⟧ˢ x)                           ≈⟨ +-cong (distribˡ _ _ _) (*-congˡ x^n₃*r≈x^i₁*p+x^i₂*q) ⟩
  x ^ n * proj₁ c₁ + x ^ n * proj₁ c₂ + x ^ n * (x ^ ⟅ i₁ ⇓⟆ * ⟦ p ⟧ˢ x + x ^ ⟅ i₂ ⇓⟆ * ⟦ q ⟧ˢ x) ≈⟨ +-congˡ (*-congˡ (+-cong (*-congʳ (x^n≈x^⁺n x i₁)) (*-congʳ (x^n≈x^⁺n x i₂)))) ⟩
  x ^ n * proj₁ c₁ + x ^ n * proj₁ c₂ + x ^ n * (x ^⁺ i₁ * ⟦ p ⟧ˢ x + x ^⁺ i₂ * ⟦ q ⟧ˢ x)          ≈⟨ +ᵖ-spine-≡-lemma₂ _ _ _ _ _ ⟩
  x ^ n * (proj₁ c₁ + x ^⁺ i₁ * ⟦ p ⟧ˢ x) + x ^ n * (proj₁ c₂ + x ^⁺ i₂ * ⟦ q ⟧ˢ x)                ∎


+ᵖ-spine-<-lemma
  : ∀ n₁ c₁ i₁ p n₂ q (n₁<n₂ : n₁ < n₂) x
  → x ^ n₁ * (c₁ + (x ^ ⟅ i₁ ⇓⟆ * ⟦ p ⟧ˢ x + x ^ (n₂ ∸ n₁) * ⟦ q ⟧ˢ x))
  ≈ x ^ n₁ * (c₁ + x ^⁺ i₁ * ⟦ p ⟧ˢ x) + x ^ n₂ * ⟦ q ⟧ˢ x
+ᵖ-spine-<-lemma n₁ c₁ i₁ p n₂ q n₁<n₂ x = begin⟨ setoid ⟩
  x ^ n₁ * (c₁ + (x ^ ⟅ i₁ ⇓⟆ * ⟦ p ⟧ˢ x + x ^ (n₂ ∸ n₁) * ⟦ q ⟧ˢ x))          ≈⟨ *-congˡ (sym (+-assoc _ _ _)) ⟩
  x ^ n₁ * ((c₁ + x ^ ⟅ i₁ ⇓⟆ * ⟦ p ⟧ˢ x) + x ^ (n₂ ∸ n₁) * ⟦ q ⟧ˢ x)          ≈⟨ distribˡ _ _ _ ⟩
  x ^ n₁ * (c₁ + x ^ ⟅ i₁ ⇓⟆ * ⟦ p ⟧ˢ x) + x ^ n₁ * (x ^ (n₂ ∸ n₁) * ⟦ q ⟧ˢ x) ≈⟨ +-cong (*-congˡ (+-congˡ (*-congʳ (x^n≈x^⁺n x i₁)))) (sym (*-assoc _ _ _)) ⟩
  x ^ n₁ * (c₁ + x ^⁺ i₁ * ⟦ p ⟧ˢ x) + (x ^ n₁ * x ^ (n₂ ∸ n₁)) * ⟦ q ⟧ˢ x     ≈⟨ +-congˡ (*-congʳ (sym (^-homo x n₁ (n₂ ∸ n₁)))) ⟩
  x ^ n₁ * (c₁ + x ^⁺ i₁ * ⟦ p ⟧ˢ x) + x ^ (n₁ +ℕ (n₂ ∸ n₁)) * ⟦ q ⟧ˢ x        ≡⟨ ≡-cong (λ t → x ^ n₁ * (c₁ + x ^⁺ i₁ * ⟦ p ⟧ˢ x) + x ^ t * ⟦ q ⟧ˢ x) (m+[n∸m]≡n (<⇒≤ n₁<n₂)) ⟩
  x ^ n₁ * (c₁ + x ^⁺ i₁ * ⟦ p ⟧ˢ x) + x ^ n₂ * ⟦ q ⟧ˢ x                       ∎

+ᵖ-spine-<-homo n₁ (K c₁) n₂ q n₁<n₂ x = begin⟨ setoid ⟩
  x ^ n₁ * (proj₁ c₁ + x ^⁺ ⟅ n₂ ∸ n₁ ⇑⟆ * ⟦ q ⟧ˢ x)          ≈⟨ distribˡ (x ^ n₁) (proj₁ c₁) (x ^⁺ ⟅ n₂ ∸ n₁ ⇑⟆ * ⟦ q ⟧ˢ x) ⟩
  x ^ n₁ * proj₁ c₁ + x ^ n₁ * (x ^⁺ ⟅ n₂ ∸ n₁ ⇑⟆ * ⟦ q ⟧ˢ x) ≈⟨ +-congˡ (sym (*-assoc (x ^ n₁) (x ^⁺ ⟅ n₂ ∸ n₁ ⇑⟆) (⟦ q ⟧ˢ x))) ⟩
  x ^ n₁ * proj₁ c₁ + (x ^ n₁ * x ^⁺ ⟅ n₂ ∸ n₁ ⇑⟆) * ⟦ q ⟧ˢ x ≈⟨ +-congˡ (*-congʳ (sym (^-^⁺-homo x n₁ ⟅ n₂ ∸ n₁ ⇑⟆))) ⟩
  x ^ n₁ * proj₁ c₁ + x ^ (n₁ +ℕ ⟅ ⟅ n₂ ∸ n₁ ⇑⟆ ⇓⟆) * ⟦ q ⟧ˢ x ≡⟨ ≡-cong (λ t → x ^ n₁ * proj₁ c₁ + x ^ t * ⟦ q ⟧ˢ x) lemma ⟩
  x ^ n₁ * proj₁ c₁ + x ^ n₂ * ⟦ q ⟧ˢ x ∎
  where
  lemma : n₁ +ℕ ⟅ ⟅ n₂ ∸ n₁ ⇑⟆ ⇓⟆ ≡ n₂
  lemma = begin⟨ ≡-setoid ℕ ⟩
    n₁ +ℕ ⟅ ⟅ n₂ ∸ n₁ ⇑⟆ ⇓⟆ ≡⟨ ≡-cong (λ x → n₁ +ℕ x) (ℕ→ℕ⁺→ℕ (n₂ ∸ n₁) {≢⇒¬≟ (m<n⇒n∸m≢0 n₁<n₂)}) ⟩
    n₁ +ℕ (n₂ ∸ n₁)         ≡⟨ m+[n∸m]≡n {n₁} {n₂} (<⇒≤ n₁<n₂) ⟩
    n₂ ∎
+ᵖ-spine-<-homo n₁ (c₁ +x^ i₁ ∙ p) n₂ q n₁<n₂ x with +ᵖ-spine ⟅ i₁ ⇓⟆ p (n₂ ∸ n₁) q | +ᵖ-spine-homo ⟅ i₁ ⇓⟆ p (n₂ ∸ n₁) q x
... | 0ᵖ | 0≈x^i₁*p+x^[n₂∸n₁]*q = begin⟨ setoid ⟩
  x ^ n₁ * proj₁ c₁                                                         ≈⟨ *-congˡ (sym (+-identityʳ (proj₁ c₁))) ⟩
  x ^ n₁ * (proj₁ c₁ + 0#)                                                  ≈⟨ *-congˡ (+-congˡ 0≈x^i₁*p+x^[n₂∸n₁]*q) ⟩
  x ^ n₁ * (proj₁ c₁ + (x ^ ⟅ i₁ ⇓⟆ * ⟦ p ⟧ˢ x + x ^ (n₂ ∸ n₁) * ⟦ q ⟧ˢ x)) ≈⟨ +ᵖ-spine-<-lemma n₁ (proj₁ c₁) i₁ p n₂ q n₁<n₂ x ⟩
  x ^ n₁ * (proj₁ c₁ + x ^⁺ i₁ * ⟦ p ⟧ˢ x) + x ^ n₂ * ⟦ q ⟧ˢ x              ∎
... | x^ zero   ∙ r | x^0*r≈x^i₁*p+x^[n₂∸n₁]*q = begin⟨ setoid ⟩
  ⟦ +ᵖ-spine-≡-K n₁ c₁ r ⟧ x                                                ≈⟨ +ᵖ-spine-≡-K-homo n₁ c₁ r x ⟩
  x ^ n₁ * (proj₁ c₁ + ⟦ r ⟧ˢ x)                                            ≈⟨ *-congˡ (+-congˡ (sym (*-identityˡ (⟦ r ⟧ˢ x)))) ⟩
  x ^ n₁ * (proj₁ c₁ + x ^ zero * ⟦ r ⟧ˢ x)                                 ≈⟨ *-congˡ (+-congˡ x^0*r≈x^i₁*p+x^[n₂∸n₁]*q) ⟩
  x ^ n₁ * (proj₁ c₁ + (x ^ ⟅ i₁ ⇓⟆ * ⟦ p ⟧ˢ x + x ^ (n₂ ∸ n₁) * ⟦ q ⟧ˢ x)) ≈⟨ +ᵖ-spine-<-lemma n₁ (proj₁ c₁) i₁ p n₂ q n₁<n₂ x ⟩
  x ^ n₁ * (proj₁ c₁ + x ^⁺ i₁ * ⟦ p ⟧ˢ x) + x ^ n₂ * ⟦ q ⟧ˢ x              ∎
... | x^ suc n₃ ∙ r | x^n₃*r≈x^i₁*p+x^[n₂∸n₁]*q = begin⟨ setoid ⟩
  x ^ n₁ * (proj₁ c₁ + x ^⁺ ⟅ suc n₃ ⇑⟆ * ⟦ r ⟧ˢ x)                         ≈⟨ *-congˡ (+-congˡ x^n₃*r≈x^i₁*p+x^[n₂∸n₁]*q) ⟩
  x ^ n₁ * (proj₁ c₁ + (x ^ ⟅ i₁ ⇓⟆ * ⟦ p ⟧ˢ x + x ^ (n₂ ∸ n₁) * ⟦ q ⟧ˢ x)) ≈⟨ +ᵖ-spine-<-lemma n₁ (proj₁ c₁) i₁ p n₂ q n₁<n₂ x ⟩
  x ^ n₁ * (proj₁ c₁ + x ^⁺ i₁ * ⟦ p ⟧ˢ x) + x ^ n₂ * ⟦ q ⟧ˢ x              ∎

+ᵖ-spine-homo n₁ p n₂ q x with <-cmp n₁ n₂
... | tri< n₁<n₂ _ _  = +ᵖ-spine-<-homo n₁ p n₂ q n₁<n₂ x
... | tri≈ _ ≡-refl _ = +ᵖ-spine-≡-homo n₁ p q x
... | tri> _ _ n₁>n₂  = begin⟨ setoid ⟩
  ⟦ +ᵖ-spine-< n₂ q n₁ p n₁>n₂ ⟧ x      ≈⟨ +ᵖ-spine-<-homo n₂ q n₁ p n₁>n₂ x ⟩
  x ^ n₂ * ⟦ q ⟧ˢ x + x ^ n₁ * ⟦ p ⟧ˢ x ≈⟨ +-comm (x ^ n₂ * ⟦ q ⟧ˢ x) (x ^ n₁ * ⟦ p ⟧ˢ x) ⟩
  x ^ n₁ * ⟦ p ⟧ˢ x + x ^ n₂ * ⟦ q ⟧ˢ x ∎

+ᵖ-homo : ∀ p q x → ⟦ p +ᵖ q ⟧ x ≈ ⟦ p ⟧ x + ⟦ q ⟧ x
+ᵖ-homo 0ᵖ q x = sym (+-identityˡ (⟦ q ⟧ x))
+ᵖ-homo (x^ o₁ ∙ p) 0ᵖ x = sym (+-identityʳ (⟦ x^ o₁ ∙ p ⟧ x))
+ᵖ-homo (x^ o₁ ∙ p) (x^ o₂ ∙ q) x = +ᵖ-spine-homo o₁ p o₂ q x

∙ᵖ-spine-homo : ∀ a p x → ⟦ ∙ᵖ-spine a p ⟧ˢ x ≈ proj₁ a * ⟦ p ⟧ˢ x
∙ᵖ-spine-homo a (K c) x = refl
∙ᵖ-spine-homo a (c +x^ m ∙ p) x = begin⟨ setoid ⟩
  proj₁ a * proj₁ c + (x ^⁺ m) * ⟦ ∙ᵖ-spine a p ⟧ˢ x  ≈⟨ +-congˡ (*-congˡ (∙ᵖ-spine-homo a p x)) ⟩
  proj₁ a * proj₁ c + (x ^⁺ m) * (proj₁ a * ⟦ p ⟧ˢ x) ≈⟨ +-congˡ (x*[y*z]≈y*[x*z] (x ^⁺ m) (proj₁ a) (⟦ p ⟧ˢ x)) ⟩
  proj₁ a * proj₁ c + proj₁ a * (x ^⁺ m * ⟦ p ⟧ˢ x)   ≈⟨ sym (distribˡ (proj₁ a) (proj₁ c) ((x ^⁺ m) * ⟦ p ⟧ˢ x)) ⟩
  proj₁ a * (proj₁ c + (x ^⁺ m) * ⟦ p ⟧ˢ x)           ∎
  where
  x*[y*z]≈y*[x*z] : ∀ x y z → x * (y * z) ≈ y * (x * z)
  x*[y*z]≈y*[x*z] = solve ACR

∙ᵖ-homo : ∀ a p x → ⟦ a ∙ᵖ p ⟧ x ≈ proj₁ a * ⟦ p ⟧ x
∙ᵖ-homo a 0ᵖ x = sym (zeroʳ (proj₁ a))
∙ᵖ-homo a (x^ n ∙ p) x = begin⟨ setoid ⟩
  x ^ n * ⟦ ∙ᵖ-spine a p ⟧ˢ x  ≈⟨ *-congˡ (∙ᵖ-spine-homo a p x) ⟩
  x ^ n * (proj₁ a * ⟦ p ⟧ˢ x) ≈⟨ sym (*-assoc (x ^ n) (proj₁ a) (⟦ p ⟧ˢ x)) ⟩
  (x ^ n * proj₁ a) * ⟦ p ⟧ˢ x ≈⟨ *-congʳ (*-comm (x ^ n) (proj₁ a)) ⟩
  (proj₁ a * x ^ n) * ⟦ p ⟧ˢ x ≈⟨ *-assoc (proj₁ a) (x ^ n) (⟦ p ⟧ˢ x) ⟩
  proj₁ a * (x ^ n * ⟦ p ⟧ˢ x) ∎

*ᵖ-homo : ∀ p q x → ⟦ p *ᵖ q ⟧ x ≈ ⟦ p ⟧ x * ⟦ q ⟧ x
*ᵖ-homo 0ᵖ q x = sym (zeroˡ (⟦ q ⟧ x))
*ᵖ-homo (x^ o₁ ∙ p) 0ᵖ x = sym (zeroʳ (x ^ o₁ * ⟦ p ⟧ˢ x))
*ᵖ-homo (x^ o₁ ∙ p) (x^ o₂ ∙ q) x = *ᵖ-spine-homo o₁ p o₂ q
  where
  final : ∀ x y z w → (x * y) * (z * w) ≈ (x * z) * (y * w)
  final = solve ACR
  lemma₁ : ∀ a b d k q → a * b * d * (k * q) ≈ a * b * (k * (d * q))
  lemma₁ a b d k q =  begin⟨ setoid ⟩
    a * b * d * (k * q)   ≈⟨ *-assoc (a * b) d (k * q) ⟩
    a * b * (d * (k * q)) ≈⟨ *-congˡ (sym (*-assoc d k q)) ⟩
    a * b * ((d * k) * q) ≈⟨ *-congˡ (*-congʳ (*-comm d k)) ⟩
    a * b * ((k * d) * q) ≈⟨ *-congˡ (*-assoc k d q) ⟩
    a * b * (k * (d * q)) ∎
  lemma₂ : ∀ o c l p → o * c * (l * p) ≈ o * (c * p * l)
  lemma₂ o c l p = begin⟨ setoid ⟩
    o * c * (l * p)   ≈⟨ *-assoc o c (l * p) ⟩
    o * (c * (l * p)) ≈⟨ *-congˡ (*-congˡ (*-comm l p)) ⟩
    o * (c * (p * l)) ≈⟨ *-congˡ (sym (*-assoc c p l)) ⟩
    o * ((c * p) * l) ∎
  lemma₃ : ∀ a c p b d q → a * c * p * (b * d * q) ≈ a * b * (c * p * (d * q))
  lemma₃ a c p b d q = begin⟨ setoid ⟩
    (a * c) * p * ((b * d) * q) ≈⟨ *-cong (*-assoc a c p) (*-assoc b d q) ⟩
    a * (c * p) * (b * (d * q)) ≈⟨ final a (c * p) b (d * q) ⟩
    a * b * (c * p * (d * q)) ∎
  mult
    : ∀ a b c d k l p q
    → (a * b) * (k * l)
    + (a * b * d) * (k * q)
    + (a * b * c) * (l * p)
    + (a * c * p) * (b * d * q)
    ≈ (a * (k + c * p)) * (b * (l + d * q))
  mult a b c d k l p q = begin⟨ setoid ⟩
    (a * b) * (k * l) + (a * b * d) * (k * q) +
    (a * b * c) * (l * p) + (a * c * p) * (b * d * q)
    ≈⟨ +-cong (+-cong (+-congˡ (lemma₁ a b d k q))
                      (lemma₂ (a * b) c l p))
              (lemma₃ a c p b d q)
     ⟩
    (a * b) * (k * l) + (a * b) * (k * (d * q)) +
    (a * b) * ((c * p) * l) + (a * b) * ((c * p) * (d * q))
    ≈⟨ +-assoc _ _ _ ⟩
    ((a * b) * (k * l) + (a * b) * (k * (d * q))) +
    ((a * b) * ((c * p) * l) + (a * b) * ((c * p) * (d * q)))
    ≈⟨ +-cong (sym (distribˡ (a * b) (k * l) (k * (d * q))))
              (sym (distribˡ (a * b) (c * p * l) ((c * p) * (d * q))))
     ⟩
    (a * b) * (k * l + k * (d * q)) +
    (a * b) * ((c * p) * l + (c * p) * (d * q))
    ≈⟨ sym (distribˡ (a * b) _ _) ⟩
    (a * b) * ((k * l + k * (d * q)) + ((c * p) * l + (c * p) * (d * q)))
    ≈⟨ *-congˡ (sym (+-assoc _ _ _)) ⟩
    (a * b) * (k * l + k * (d * q) + (c * p) * l + (c * p) * (d * q))
    ≈⟨ *-congˡ (sym (foil k (c * p) l (d * q))) ⟩
    (a * b) * ((k + c * p) * (l + d * q))
    ≈⟨ final a b (k + c * p) (l + d * q) ⟩
    (a * (k + c * p)) * (b * (l + d * q)) ∎

  *ᵖ-spine-homo : ∀ o₁ p o₂ q → ⟦ *ᵖ-spine o₁ p o₂ q ⟧ x ≈ (x ^ o₁ * ⟦ p ⟧ˢ x) * (x ^ o₂ * ⟦ q ⟧ˢ x)
  *ᵖ-spine-homo o₁ (K c₁) o₂ q = begin⟨ setoid ⟩
    x ^ (o₁ +ℕ o₂) * ⟦ ∙ᵖ-spine c₁ q ⟧ˢ x     ≈⟨ *-congˡ (∙ᵖ-spine-homo c₁ q x) ⟩
    x ^ (o₁ +ℕ o₂) * (proj₁ c₁ * ⟦ q ⟧ˢ x)    ≈⟨ *-congʳ (^-homo x o₁ o₂) ⟩
    (x ^ o₁ * x ^ o₂) * (proj₁ c₁ * ⟦ q ⟧ˢ x) ≈⟨ final (x ^ o₁) (x ^ o₂) (proj₁ c₁) (⟦ q ⟧ˢ x)  ⟩
    (x ^ o₁ * proj₁ c₁) * (x ^ o₂ * ⟦ q ⟧ˢ x) ∎
  *ᵖ-spine-homo o₁ (c₁ +x^ n₁ ∙ p) o₂ (K c₂) = begin⟨ setoid ⟩
    x ^ (o₁ +ℕ o₂) * (proj₁ c₂ * proj₁ c₁ + (x ^⁺ n₁) * ⟦ ∙ᵖ-spine c₂ p ⟧ˢ x)     ≈⟨ *-cong (^-homo x o₁ o₂) (+-cong (*-comm (proj₁ c₂) (proj₁ c₁)) (*-congˡ (∙ᵖ-spine-homo c₂ p x))) ⟩
    (x ^ o₁ * x ^ o₂) * (proj₁ c₁ * proj₁ c₂ + (x ^⁺ n₁) * (proj₁ c₂ * ⟦ p ⟧ˢ x)) ≈⟨ *-congˡ (+-congˡ (*-congˡ (*-comm (proj₁ c₂) (⟦ p ⟧ˢ x)))) ⟩
    (x ^ o₁ * x ^ o₂) * (proj₁ c₁ * proj₁ c₂ + (x ^⁺ n₁) * (⟦ p ⟧ˢ x * proj₁ c₂)) ≈⟨ *-congˡ (+-congˡ (sym (*-assoc (x ^⁺ n₁) (⟦ p ⟧ˢ x) (proj₁ c₂)))) ⟩
    (x ^ o₁ * x ^ o₂) * (proj₁ c₁ * proj₁ c₂ + (x ^⁺ n₁ * ⟦ p ⟧ˢ x) * proj₁ c₂)   ≈⟨ *-congˡ (sym (distribʳ (proj₁ c₂) (proj₁ c₁) (x ^⁺ n₁ * ⟦ p ⟧ˢ x))) ⟩
    (x ^ o₁ * x ^ o₂) * ((proj₁ c₁ + (x ^⁺ n₁ * ⟦ p ⟧ˢ x)) * proj₁ c₂)            ≈⟨ final (x ^ o₁) (x ^ o₂) (proj₁ c₁ + (x ^⁺ n₁ * ⟦ p ⟧ˢ x)) (proj₁ c₂) ⟩
    x ^ o₁ * (proj₁ c₁ + (x ^⁺ n₁) * ⟦ p ⟧ˢ x) * (x ^ o₂ * proj₁ c₂)              ∎
  *ᵖ-spine-homo o₁ (c₁ +x^ n₁ ∙ p) o₂ (c₂ +x^ n₂ ∙ q) = begin⟨ setoid ⟩
    ⟦ x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂)
    +ᵖ c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q
    +ᵖ c₂ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p
    +ᵖ *ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q ⟧ x
    ≈⟨ +ᵖ-homo (x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) +ᵖ
                c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q +ᵖ
                c₂ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p)
               (*ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q) x
     ⟩
    ⟦ x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂)
    +ᵖ c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q
    +ᵖ c₂ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p ⟧ x
    + ⟦ *ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q ⟧ x
    ≈⟨ +-cong (+ᵖ-homo (x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) +ᵖ
                        c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q)
                       (c₂ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p) x)
              (*ᵖ-spine-homo (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q)
     ⟩
    ⟦ x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂)
    +ᵖ c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q ⟧ x
    + ⟦ c₂ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p ⟧ x
    + (x ^ (o₁ +ℕ ⟅ n₁ ⇓⟆) * ⟦ p ⟧ˢ x) * (x ^ (o₂ +ℕ ⟅ n₂ ⇓⟆) * ⟦ q ⟧ˢ x)
    ≈⟨ +-cong (+-cong (+ᵖ-homo (x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂))
                               (c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q) x)
                      (*-cong  (^-^⁺-homo x (o₁ +ℕ o₂) n₁)
                               (∙ᵖ-spine-homo c₂ p x)))
              (*-cong (*-congʳ (^-^⁺-homo x o₁ n₁))
                      (*-congʳ (^-^⁺-homo x o₂ n₂)))
     ⟩
    ⟦ x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) ⟧ x
    + ⟦ c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q ⟧ x
    + (x ^ (o₁ +ℕ o₂) * x ^⁺ n₁) * (proj₁ c₂ * ⟦ p ⟧ˢ x)
    + ((x ^ o₁ * x ^⁺ n₁) * ⟦ p ⟧ˢ x) * ((x ^ o₂ * x ^⁺ n₂) * ⟦ q ⟧ˢ x)
    ≈⟨ +-congʳ (+-cong (+-cong (*-congʳ (^-homo x o₁ o₂))
                               (*-cong  (^-^⁺-homo x (o₁ +ℕ o₂) n₂)
                                        (∙ᵖ-spine-homo c₁ q x)))
                       (*-congʳ (*-congʳ (^-homo x o₁ o₂)))) ⟩
      (x ^ o₁ * x ^ o₂) * (proj₁ c₁ * proj₁ c₂)
    + (x ^ (o₁ +ℕ o₂) * x ^⁺ n₂) * (proj₁ c₁ * ⟦ q ⟧ˢ x)
    + (x ^ o₁ * x ^ o₂ * x ^⁺ n₁) * (proj₁ c₂ * ⟦ p ⟧ˢ x)
    + ((x ^ o₁ * x ^⁺ n₁) * ⟦ p ⟧ˢ x) * ((x ^ o₂ * x ^⁺ n₂) * ⟦ q ⟧ˢ x)
    ≈⟨ +-congʳ (+-congʳ (+-congˡ (*-congʳ (*-congʳ (^-homo x o₁ o₂))))) ⟩
      (x ^ o₁ * x ^ o₂) * (proj₁ c₁ * proj₁ c₂)
    + ((x ^ o₁ * x ^ o₂) * x ^⁺ n₂) * (proj₁ c₁ * ⟦ q ⟧ˢ x)
    + (x ^ o₁ * x ^ o₂ * x ^⁺ n₁) * (proj₁ c₂ * ⟦ p ⟧ˢ x)
    + ((x ^ o₁ * x ^⁺ n₁) * ⟦ p ⟧ˢ x) * ((x ^ o₂ * x ^⁺ n₂) * ⟦ q ⟧ˢ x)
    ≈⟨ mult (x ^ o₁) (x ^ o₂) (x ^⁺ n₁) (x ^⁺ n₂) (proj₁ c₁) (proj₁ c₂) (⟦ p ⟧ˢ x) (⟦ q ⟧ˢ x) ⟩
    ((x ^ o₁) * (proj₁ c₁ + (x ^⁺ n₁) * ⟦ p ⟧ˢ x)) *
    ((x ^ o₂) * (proj₁ c₂ + (x ^⁺ n₂) * ⟦ q ⟧ˢ x)) ∎

-ᵖ‿homo : ∀ p x → ⟦ -ᵖ p ⟧ x ≈ - ⟦ p ⟧ x
-ᵖ‿homo p x = begin⟨ setoid ⟩
  ⟦ -1#-nonzero ∙ᵖ p ⟧ x ≈⟨ ∙ᵖ-homo -1#-nonzero p x ⟩
  - 1# * ⟦ p ⟧ x         ≈⟨ sym (-‿distribˡ-* 1# (⟦ p ⟧ x)) ⟩
  - (1# * ⟦ p ⟧ x)       ≈⟨ -‿cong (*-identityˡ (⟦ p ⟧ x)) ⟩
  - ⟦ p ⟧ x              ∎

+ᵖ-cong : Congruent₂ _+ᵖ_
+ᵖ-cong {p} {q} {r} {s} (≈✓ ∀x[pₓ≈qₓ]) (≈✓ ∀x[rₓ≈sₓ]) = ≈✓ λ x → begin⟨ setoid ⟩
  ⟦ p +ᵖ r ⟧ x ≈⟨ +ᵖ-homo p r x ⟩
  ⟦ p ⟧ x + ⟦ r ⟧ x ≈⟨ +-cong (∀x[pₓ≈qₓ] x) (∀x[rₓ≈sₓ] x)  ⟩
  ⟦ q ⟧ x + ⟦ s ⟧ x ≈⟨ sym (+ᵖ-homo q s x) ⟩
  ⟦ q +ᵖ s ⟧ x ∎

+ᵖ-isMagma : IsMagma _+ᵖ_
+ᵖ-isMagma = record
  { isEquivalence = ≈ᵖ-isEquivalence
  ; ∙-cong = +ᵖ-cong
  }

+ᵖ-assoc : Associative _+ᵖ_
+ᵖ-assoc p q r = ≈✓ λ x → begin⟨ setoid ⟩
  ⟦ p +ᵖ q +ᵖ r ⟧ x ≈⟨ +ᵖ-homo (p +ᵖ q) r x ⟩
  ⟦ p +ᵖ q ⟧ x + ⟦ r ⟧ x ≈⟨ +-congʳ (+ᵖ-homo p q x) ⟩
  ⟦ p ⟧ x + ⟦ q ⟧ x + ⟦ r ⟧ x ≈⟨ +-assoc (⟦ p ⟧ x) (⟦ q ⟧ x) (⟦ r ⟧ x) ⟩
  ⟦ p ⟧ x + (⟦ q ⟧ x + ⟦ r ⟧ x) ≈⟨ +-congˡ (sym (+ᵖ-homo q r x)) ⟩
  ⟦ p ⟧ x + ⟦ q +ᵖ r ⟧ x ≈⟨ sym (+ᵖ-homo p (q +ᵖ r) x) ⟩
  ⟦ p +ᵖ (q +ᵖ r) ⟧ x ∎

+ᵖ-isSemigroup : IsSemigroup _+ᵖ_
+ᵖ-isSemigroup = record
  { isMagma = +ᵖ-isMagma
  ; assoc = +ᵖ-assoc
  }

+ᵖ-comm : Commutative _+ᵖ_
+ᵖ-comm p q = ≈✓ λ x → begin⟨ setoid ⟩
  ⟦ p +ᵖ q ⟧ x ≈⟨ +ᵖ-homo p q x ⟩
  ⟦ p ⟧ x + ⟦ q ⟧ x ≈⟨ +-comm (⟦ p ⟧ x) (⟦ q ⟧ x) ⟩
  ⟦ q ⟧ x + ⟦ p ⟧ x ≈⟨ sym (+ᵖ-homo q p x) ⟩
  ⟦ q +ᵖ p ⟧ x ∎

+ᵖ-identityˡ : LeftIdentity 0ᵖ _+ᵖ_
+ᵖ-identityˡ p = ≈✓ λ x → begin⟨ setoid ⟩
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
-ᵖ‿inverseˡ p = ≈✓ λ x → begin⟨ setoid ⟩
  ⟦ -ᵖ p +ᵖ p ⟧ x      ≈⟨ +ᵖ-homo (-ᵖ p) p x ⟩
  ⟦ -ᵖ p ⟧ x + ⟦ p ⟧ x ≈⟨ +-congʳ (-ᵖ‿homo p x) ⟩
  - ⟦ p ⟧ x + ⟦ p ⟧ x  ≈⟨ -‿inverseˡ (⟦ p ⟧ x) ⟩
  ⟦ 0ᵖ ⟧ x             ∎

-ᵖ‿inverseʳ : RightInverse 0ᵖ -ᵖ_ _+ᵖ_
-ᵖ‿inverseʳ = comm+invˡ⇒invʳ +ᵖ-comm -ᵖ‿inverseˡ

-ᵖ‿inverse : Inverse 0ᵖ -ᵖ_ _+ᵖ_
-ᵖ‿inverse = -ᵖ‿inverseˡ , -ᵖ‿inverseʳ

-ᵖ‿cong : Congruent₁ (-ᵖ_)
-ᵖ‿cong {p} {q} (≈✓ ∀x[pₓ≈qₓ]) = ≈✓ λ x → begin⟨ setoid ⟩
  ⟦ -ᵖ p ⟧ x ≈⟨ -ᵖ‿homo p x ⟩
  - ⟦ p ⟧ x  ≈⟨ -‿cong (∀x[pₓ≈qₓ] x) ⟩
  - ⟦ q ⟧ x  ≈⟨ sym (-ᵖ‿homo q x) ⟩
  ⟦ -ᵖ q ⟧ x ∎

+ᵖ-isGroup : IsGroup _+ᵖ_ 0ᵖ (-ᵖ_)
+ᵖ-isGroup = record
  { isMonoid = +ᵖ-isMonoid
  ; inverse = -ᵖ‿inverse
  ; ⁻¹-cong = -ᵖ‿cong
  }

+ᵖ-isAbelianGroup : IsAbelianGroup _+ᵖ_ 0ᵖ (-ᵖ_)
+ᵖ-isAbelianGroup = record
  { isGroup = +ᵖ-isGroup
  ; comm = +ᵖ-comm
  }

*ᵖ-cong : Congruent₂ _*ᵖ_
*ᵖ-cong {p} {q} {r} {s} (≈✓ ∀x[pₓ≈qₓ]) (≈✓ ∀x[rₓ≈sₓ]) = ≈✓ λ x → begin⟨ setoid ⟩
  ⟦ p *ᵖ r ⟧ x ≈⟨ *ᵖ-homo p r x ⟩
  ⟦ p ⟧ x * ⟦ r ⟧ x ≈⟨ *-cong (∀x[pₓ≈qₓ] x) (∀x[rₓ≈sₓ] x)  ⟩
  ⟦ q ⟧ x * ⟦ s ⟧ x ≈⟨ sym (*ᵖ-homo q s x) ⟩
  ⟦ q *ᵖ s ⟧ x ∎

*ᵖ-isMagma : IsMagma _*ᵖ_
*ᵖ-isMagma = record
  { isEquivalence = ≈ᵖ-isEquivalence
  ; ∙-cong = *ᵖ-cong
  }

*ᵖ-assoc : Associative _*ᵖ_
*ᵖ-assoc p q r = ≈✓ λ x → begin⟨ setoid ⟩
  ⟦ p *ᵖ q *ᵖ r ⟧ x ≈⟨ *ᵖ-homo (p *ᵖ q) r x ⟩
  ⟦ p *ᵖ q ⟧ x * ⟦ r ⟧ x ≈⟨ *-congʳ (*ᵖ-homo p q x) ⟩
  ⟦ p ⟧ x * ⟦ q ⟧ x * ⟦ r ⟧ x ≈⟨ *-assoc (⟦ p ⟧ x) (⟦ q ⟧ x) (⟦ r ⟧ x) ⟩
  ⟦ p ⟧ x * (⟦ q ⟧ x * ⟦ r ⟧ x) ≈⟨ *-congˡ (sym (*ᵖ-homo q r x)) ⟩
  ⟦ p ⟧ x * ⟦ q *ᵖ r ⟧ x ≈⟨ sym (*ᵖ-homo p (q *ᵖ r) x) ⟩
  ⟦ p *ᵖ (q *ᵖ r) ⟧ x ∎

*ᵖ-isSemigroup : IsSemigroup _*ᵖ_
*ᵖ-isSemigroup = record
  { isMagma = *ᵖ-isMagma
  ; assoc = *ᵖ-assoc
  }

*ᵖ-comm : Commutative _*ᵖ_
*ᵖ-comm p q = ≈✓ λ x → begin⟨ setoid ⟩
  ⟦ p *ᵖ q ⟧ x ≈⟨ *ᵖ-homo p q x ⟩
  ⟦ p ⟧ x * ⟦ q ⟧ x ≈⟨ *-comm (⟦ p ⟧ x) (⟦ q ⟧ x) ⟩
  ⟦ q ⟧ x * ⟦ p ⟧ x ≈⟨ sym (*ᵖ-homo q p x) ⟩
  ⟦ q *ᵖ p ⟧ x ∎

*ᵖ-identityˡ : LeftIdentity 1ᵖ _*ᵖ_
*ᵖ-identityˡ p = ≈✓ λ x → begin⟨ setoid ⟩
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
*ᵖ-distribˡ-+ᵖ p q r = ≈✓ λ x → begin⟨ setoid ⟩
  ⟦ p *ᵖ (q +ᵖ r) ⟧ x                   ≈⟨ *ᵖ-homo p (q +ᵖ r) x ⟩
  ⟦ p ⟧ x * ⟦ q +ᵖ r ⟧ x                ≈⟨ *-congˡ (+ᵖ-homo q r x)  ⟩
  ⟦ p ⟧ x * (⟦ q ⟧ x + ⟦ r ⟧ x)         ≈⟨ distribˡ (⟦ p ⟧ x) (⟦ q ⟧ x) (⟦ r ⟧ x) ⟩
  ⟦ p ⟧ x * ⟦ q ⟧ x + ⟦ p ⟧ x * ⟦ r ⟧ x ≈⟨ +-cong (sym (*ᵖ-homo p q x)) (sym (*ᵖ-homo p r x)) ⟩
  ⟦ p *ᵖ q ⟧ x + ⟦ p *ᵖ r ⟧ x           ≈⟨ sym (+ᵖ-homo (p *ᵖ q) (p *ᵖ r) x) ⟩
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

0ᵖ≉1ᵖ : 0ᵖ ≉ᵖ 1ᵖ
0ᵖ≉1ᵖ (≈✓ ∀x[0≈x^0*1])= 0#≉1# $ begin⟨ setoid ⟩
  0# ≈⟨ ∀x[0≈x^0*1] 1# ⟩
  1# * 1# ≈⟨ *-identityʳ 1# ⟩
  1# ∎

+ᵖ-*ᵖ-isNonZeroCommutativeRing : IsNonZeroCommutativeRing _+ᵖ_ _*ᵖ_ -ᵖ_ 0ᵖ 1ᵖ
+ᵖ-*ᵖ-isNonZeroCommutativeRing = record
  { isCommutativeRing = +ᵖ-*ᵖ-isCommutativeRing
  ; 0#≉1# = 0ᵖ≉1ᵖ
  }


-- x≉0⇒x^n≉0 : ∀ x (x≉0 : x ≉ 0#) n → x ^ n ≉ 0#
-- x≉0⇒x^n≉0 = {!!}

-- *ᵖ-cancelˡ : ∀ p {q r} → p ≉ᵖ 0ᵖ → p *ᵖ q ≈ᵖ p *ᵖ r → q ≈ᵖ r
-- *ᵖ-cancelˡ 0ᵖ {q} {r} p≉0 (≈✓ ∀x[p*q≈p*r]) = contradiction ≈ᵖ-refl p≉0
-- *ᵖ-cancelˡ (x^ n ∙ p) {q} {r} p≉0 (≈✓ ∀x[p*q≈p*r]) = ≈✓ ∀x[qₓ≈rₓ]
--   where
--   ∀x[qₓ≈rₓ] : ∀ x → ⟦ q ⟧ x ≈ ⟦ r ⟧ x
--   ∀x[qₓ≈rₓ] x with x ≈? 0#
--   ... | yes x≈0 = {!!}
--   ... | no  x≉0 = *-cancelˡ (x ^ n) (x≉0⇒x^n≉0 x x≉0 n) {!!}

-- +ᵖ-*ᵖ-isIntegralDomain : IsIntegralDomain _+ᵖ_ _*ᵖ_ -ᵖ_ 0ᵖ 1ᵖ
-- +ᵖ-*ᵖ-isIntegralDomain = record
--   { isNonZeroCommutativeRing = +ᵖ-*ᵖ-isNonZeroCommutativeRing
--   ; *-cancelˡ = {!!}
--   }

-- open import AKS.Unsafe using (TODO)

-- lc : ∀ p {p≉0 : p ≉ᵖ 0ᵖ} → C/0
-- lc 0ᵖ {p≉0} = contradiction ≈ᵖ-refl p≉0
-- lc (x^ n ∙ p) {p≉0} = lc-spine p
--   where
--   lc-spine : Spine → C/0
--   lc-spine (K c) = c
--   lc-spine (c +x^ n ∙ p) = lc-spine p

-- infix 4 _≈ᵖ?_
-- _≈ᵖ?_ : Decidable _≈ᵖ_
-- _divᵖ_ : ∀ (n m : Polynomial) {m≉0 : m ≉ᵖ 0ᵖ} → Polynomial

-- (n divᵖ m) {m≉0} with n ≈ᵖ? 0ᵖ
-- ... | yes n≈0 = 0ᵖ
-- ... | no  n≉0 = loop 0ᵖ n {n≉0} <-well-founded
--   where
--   leading : ∀ r {r≉0 : r ≉ᵖ 0ᵖ} → Polynomial
--   leading r {r≉0} = (lc r {r≉0} /-nonzero lc m {m≉0}) ∙𝑋^ (deg r {r≉0} ∸ deg m {m≉0})
--   loop : ∀ (q r : Polynomial) {r≉0} → Acc _<_ (deg r {r≉0}) → Polynomial
--   loop q r {r≉0} (acc downward) with <-≤-connex (deg r {r≉0}) (deg m {m≉0})
--   ... | inj₁ r<m = q
--   ... | inj₂ r≥m with r -ᵖ leading r {r≉0} *ᵖ m ≈ᵖ? 0ᵖ
--   ...   | yes r'≈0 = q
--   ...   | no  r'≉0 = loop (q +ᵖ leading r {r≉0}) (r -ᵖ leading r {r≉0} *ᵖ m) {r'≉0} (downward _ TODO)

-- ≈ᵖ⇒≈ⁱ : ∀ {p q} → p ≈ᵖ q → p ≈ⁱ q
-- ≈ᵖ⇒≈ⁱ {0ᵖ} {0ᵖ} p≈ᵖq = 0ᵖ≈
-- ≈ᵖ⇒≈ⁱ {0ᵖ} {x^ o₂ ∙ q} (≈✓ ∀x[pₓ≈qₓ]) = TODO
-- ≈ᵖ⇒≈ⁱ {x^ o₁ ∙ p} {0ᵖ} p≈ᵖq = TODO
-- ≈ᵖ⇒≈ⁱ {x^ o₁ ∙ p} {x^ o₂ ∙ q} (≈✓ ∀x[pₓ≈qₓ]) = 0ᵖ≉ {!!} {!!}

-- p ≈ᵖ? q = map (FE.equivalence ≈ⁱ⇒≈ᵖ ≈ᵖ⇒≈ⁱ) (p ≈ⁱ? q)
