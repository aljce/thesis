open import Level using () renaming (_⊔_ to _⊔ˡ_)

open import Data.Product using (_,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Reflexive; Symmetric; Transitive; Setoid; Tri)
open Tri
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_) renaming (refl to ≡-refl; sym to ≡-sym)
open import Algebra.Bundles using (RawRing)
open import AKS.Algebra.Bundles using (DecField)

module AKS.Polynomial.Base {c ℓ} (F : DecField c ℓ)  where

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.FromNat using (Number)
open import AKS.Nat using (ℕ; _∸_; _<_; lte) renaming (_+_ to _+ℕ_; _⊔_ to _⊔ℕ_)
open ℕ
open import AKS.Nat using (≢⇒¬≟; <-cmp; m<n⇒n∸m≢0)
open import AKS.Nat using (ℕ⁺; ⟅_⇓⟆; ⟅_⇑⟆)
open import AKS.Nat.WellFounded using (Acc; acc; <-well-founded)

open DecField F
  using (0#; 1#; _+_; _*_; -_; _-_; _⁻¹; _/_; C/0)
  renaming (Carrier to C)
open DecField F using (_≈_; _≈?_; setoid)
open Setoid setoid using (refl; sym; trans)
open DecField F
  using (*-commutativeMonoid; 1#-nonzero; -1#-nonzero; _*-nonzero_; _/-nonzero_)
open import AKS.Exponentiation *-commutativeMonoid using (_^_; _^⁺_)

data Spine : Set (c ⊔ˡ ℓ) where
  K : C/0 → Spine
  _+x^_∙_ : C/0 → ℕ⁺ → Spine → Spine

data Polynomial : Set (c ⊔ˡ ℓ) where
  0ᵖ : Polynomial
  x^_∙_ : ℕ → Spine → Polynomial

⟦_⟧ˢ : Spine → C → C
⟦ K c ⟧ˢ x = proj₁ c
⟦ c +x^ n ∙ p ⟧ˢ x = proj₁ c + x ^⁺ n * ⟦ p ⟧ˢ x

⟦_⟧ : Polynomial → C → C
⟦ 0ᵖ ⟧ x = 0#
⟦ x^ n ∙ p ⟧ x = x ^ n * ⟦ p ⟧ˢ x

1ᵖ : Polynomial
1ᵖ = x^ 0 ∙ K 1#-nonzero

_+?_ : ∀ (k₁ k₂ : C/0) → (proj₁ k₁ + proj₁ k₂ ≈ 0#) ⊎ C/0
k₁ +? k₂ with proj₁ k₁ + proj₁ k₂ ≈? 0#
... | yes k₁+k₂≈0 = inj₁ k₁+k₂≈0
... | no  k₁+k₂≉0 = inj₂ (proj₁ k₁ + proj₁ k₂ , k₁+k₂≉0)

+ᵖ-spine-≡-K : ℕ → C/0 → Spine → Polynomial
+ᵖ-spine-≡-K n c₁ (K c₂) with c₁ +? c₂
... | inj₁ _ = 0ᵖ
... | inj₂ c₁+c₂ = x^ n ∙ K c₁+c₂
+ᵖ-spine-≡-K n c₁ (c₂ +x^ i₂ ∙ q) with c₁ +? c₂
... | inj₁ _ = x^ (n +ℕ ⟅ i₂ ⇓⟆) ∙ q
... | inj₂ c₁+c₂ = x^ n ∙ (c₁+c₂ +x^ i₂ ∙ q)

+ᵖ-spine-≡ : ℕ → Spine → Spine → Polynomial
+ᵖ-spine-< : (n : ℕ) → Spine → (m : ℕ) → Spine → n < m → Polynomial
+ᵖ-spine : ℕ → Spine → ℕ → Spine → Polynomial

+ᵖ-spine-≡ n (K c₁) q = +ᵖ-spine-≡-K n c₁ q
+ᵖ-spine-≡ n (c₁ +x^ i₁ ∙ p) (K c₂) = +ᵖ-spine-≡-K n c₂ (c₁ +x^ i₁ ∙ p)
+ᵖ-spine-≡ n (c₁ +x^ i₁ ∙ p) (c₂ +x^ i₂ ∙ q) with c₁ +? c₂
... | inj₁ _ = +ᵖ-spine (n +ℕ ⟅ i₁ ⇓⟆) p (n +ℕ ⟅ i₂ ⇓⟆) q
... | inj₂ c₁+c₂ with +ᵖ-spine ⟅ i₁ ⇓⟆ p ⟅ i₂ ⇓⟆ q
...   | 0ᵖ = x^ n ∙ K c₁+c₂
...   | x^ zero ∙ r = +ᵖ-spine-≡-K n c₁+c₂ r
...   | x^ suc n₃ ∙ r = x^ n ∙ (c₁+c₂ +x^ ⟅ suc n₃ ⇑⟆ ∙ r)

+ᵖ-spine-< n₁ (K c₁) n₂ q n₁<n₂ = x^ n₁ ∙ (c₁ +x^ ⟅ n₂ ∸ n₁ ⇑⟆ {≢⇒¬≟ (m<n⇒n∸m≢0 n₁<n₂)} ∙ q)
+ᵖ-spine-< n₁ (c₁ +x^ i₁ ∙ p) n₂ q n₁<n₂ with +ᵖ-spine ⟅ i₁ ⇓⟆ p (n₂ ∸ n₁) q
... | 0ᵖ = x^ n₁ ∙ K c₁
... | x^ zero ∙ r = +ᵖ-spine-≡-K n₁ c₁ r
... | x^ suc n₃ ∙ r = x^ n₁ ∙ (c₁ +x^ ⟅ suc n₃ ⇑⟆ ∙ r)

+ᵖ-spine n₁ p n₂ q with <-cmp n₁ n₂
... | tri< n₁<n₂ _ _ = +ᵖ-spine-< n₁ p n₂ q n₁<n₂
... | tri≈ _ n₁≡n₂ _ = +ᵖ-spine-≡ n₁ p q
... | tri> _ _ n₁>n₂ = +ᵖ-spine-< n₂ q n₁ p n₁>n₂

infixl 6 _+ᵖ_
_+ᵖ_ : Polynomial → Polynomial → Polynomial
0ᵖ +ᵖ q = q
(x^ n₁ ∙ p) +ᵖ 0ᵖ = x^ n₁ ∙ p
(x^ n₁ ∙ p) +ᵖ (x^ n₂ ∙ q) = +ᵖ-spine n₁ p n₂ q

𝑋^_ : ℕ → Polynomial
𝑋^ n = x^ n ∙ K 1#-nonzero

_∙𝑋^_ : C/0 → ℕ → Polynomial
c ∙𝑋^ n = x^ n ∙ K c

∙ᵖ-spine : C/0 → Spine → Spine
∙ᵖ-spine c₁ (K c₂) = K (c₁ *-nonzero c₂)
∙ᵖ-spine c₁ (c₂ +x^ n ∙ p) = (c₁ *-nonzero c₂) +x^ n ∙ (∙ᵖ-spine c₁ p)

infixl 7 _∙ᵖ_
_∙ᵖ_ : C/0 → Polynomial → Polynomial
c ∙ᵖ 0ᵖ = 0ᵖ
c ∙ᵖ (x^ n ∙ p) = x^ n ∙ (∙ᵖ-spine c p)

*ᵖ-spine : ℕ → Spine → ℕ → Spine → Polynomial
*ᵖ-spine o₁ (K c₁) o₂ q = x^ (o₁ +ℕ o₂) ∙ (∙ᵖ-spine c₁ q)
*ᵖ-spine o₁ (c₁ +x^ n₁ ∙ p) o₂ (K c₂) = x^ (o₁ +ℕ o₂) ∙ (∙ᵖ-spine c₂ (c₁ +x^ n₁ ∙ p))
*ᵖ-spine o₁ (c₁ +x^ n₁ ∙ p) o₂ (c₂ +x^ n₂ ∙ q) =
  x^ (o₁ +ℕ o₂) ∙ K (c₁ *-nonzero c₂) +ᵖ
  c₁ ∙ᵖ x^ (o₁ +ℕ o₂ +ℕ ⟅ n₂ ⇓⟆) ∙ q +ᵖ
  c₂ ∙ᵖ (x^ (o₁ +ℕ o₂ +ℕ ⟅ n₁ ⇓⟆) ∙ p) +ᵖ
  *ᵖ-spine (o₁ +ℕ ⟅ n₁ ⇓⟆) p (o₂ +ℕ ⟅ n₂ ⇓⟆) q
-- (c₁ + x ^ n₁ * p[x]) * (c₂ + x ^ n₂ * q[x]) = (c₁ * c₂) + (c₁ * x ^ n₂ * q[x]) + (x ^ n₁ * p[x] * c₂) + (x ^ n₁ * p[x] * x ^ n₂ * q[x])

infixl 7 _*ᵖ_
_*ᵖ_ : Polynomial → Polynomial → Polynomial
0ᵖ *ᵖ q = 0ᵖ
(x^ n₁ ∙ p) *ᵖ 0ᵖ = 0ᵖ
(x^ n₁ ∙ p) *ᵖ (x^ n₂ ∙ q) = *ᵖ-spine n₁ p n₂ q

-ᵖ_ : Polynomial → Polynomial
-ᵖ p = -1#-nonzero ∙ᵖ p

infixl 6 _-ᵖ_
_-ᵖ_ : Polynomial → Polynomial → Polynomial
p -ᵖ q = p +ᵖ (-ᵖ q)

infix 4 _≈ᵖ_
record _≈ᵖ_ (p : Polynomial) (q : Polynomial) : Set (c ⊔ˡ ℓ) where
  constructor ≈✓
  field
    ∀x[pₓ≈qₓ] : ∀ x → ⟦ p ⟧ x ≈ ⟦ q ⟧ x

infix 4 _≉ᵖ_
_≉ᵖ_ : Polynomial → Polynomial → Set (c ⊔ˡ ℓ)
p ≉ᵖ q = ¬ (p ≈ᵖ q)

≈ᵖ-refl : Reflexive _≈ᵖ_
≈ᵖ-refl = ≈✓ λ x → refl

≈ᵖ-sym : Symmetric _≈ᵖ_
≈ᵖ-sym (≈✓ ∀x[pₓ≈qₓ]) = ≈✓ (λ x → sym (∀x[pₓ≈qₓ] x))

≈ᵖ-trans : Transitive _≈ᵖ_
≈ᵖ-trans (≈✓ ∀x[pₓ≈qₓ]) (≈✓ ∀x[qₓ≈rₓ]) = ≈✓ (λ x → trans (∀x[pₓ≈qₓ] x) (∀x[qₓ≈rₓ] x))

data _≈ˢ_ : Spine → Spine → Set (c ⊔ˡ ℓ) where
  K≈ : ∀ {c₁ c₂} → proj₁ c₁ ≈ proj₁ c₂ → K c₁ ≈ˢ K c₂
  +≈ : ∀ {c₁ c₂} {n₁ n₂} {p q} → proj₁ c₁ ≈ proj₁ c₂ → n₁ ≡ n₂ → p ≈ˢ q → (c₁ +x^ n₁ ∙ p) ≈ˢ (c₂ +x^ n₂ ∙ q)

infix 4 _≈ⁱ_
data _≈ⁱ_ : Polynomial → Polynomial → Set (c ⊔ˡ ℓ) where
  0ᵖ≈ : 0ᵖ ≈ⁱ 0ᵖ
  0ᵖ≉ : ∀ {o₁ o₂} {p q} → o₁ ≡ o₂ → p ≈ˢ q → x^ o₁ ∙ p ≈ⁱ x^ o₂ ∙ q

infix 4 _≉ⁱ_
_≉ⁱ_ : Polynomial → Polynomial → Set (c ⊔ˡ ℓ)
p ≉ⁱ q = ¬ (p ≈ⁱ q)

≈ⁱ-refl : Reflexive _≈ⁱ_
≈ⁱ-refl {0ᵖ} = 0ᵖ≈
≈ⁱ-refl {x^ n ∙ p} = 0ᵖ≉ ≡-refl ≈ˢ-refl
  where
  ≈ˢ-refl : Reflexive _≈ˢ_
  ≈ˢ-refl {K c} = K≈ refl
  ≈ˢ-refl {c +x^ n ∙ p} = +≈ refl ≡-refl ≈ˢ-refl

≈ⁱ-sym : Symmetric _≈ⁱ_
≈ⁱ-sym {0ᵖ} {0ᵖ} 0ᵖ≈ = 0ᵖ≈
≈ⁱ-sym {x^ n ∙ p} {x^ n ∙ q} (0ᵖ≉ ≡-refl p≈ˢq) = 0ᵖ≉ ≡-refl (≈ˢ-sym p≈ˢq)
  where
  ≈ˢ-sym : Symmetric _≈ˢ_
  ≈ˢ-sym {K c₁} {K c₂} (K≈ c₁≈c₂) = K≈ (sym c₁≈c₂)
  ≈ˢ-sym {c₁ +x^ n ∙ p} {c₂ +x^ n ∙ q} (+≈ c₁≈c₂ ≡-refl p≈ˢq) = +≈ (sym c₁≈c₂) ≡-refl (≈ˢ-sym p≈ˢq)

≈ⁱ-trans : Transitive _≈ⁱ_
≈ⁱ-trans {0ᵖ} {0ᵖ} {0ᵖ} 0ᵖ≈ 0ᵖ≈ = 0ᵖ≈
≈ⁱ-trans {_}  {_}  {_} (0ᵖ≉ ≡-refl p≈ˢq) (0ᵖ≉ ≡-refl q≈ˢr) = 0ᵖ≉ ≡-refl (≈ˢ-trans p≈ˢq q≈ˢr)
  where
  ≈ˢ-trans : Transitive _≈ˢ_
  ≈ˢ-trans (K≈ c₁≈c₂) (K≈ c₂≈c₃) = K≈ (trans c₁≈c₂ c₂≈c₃)
  ≈ˢ-trans (+≈ c₁≈c₂ ≡-refl p≈ˢq) (+≈ c₂≈c₃ ≡-refl q≈ˢr) = +≈ (trans c₁≈c₂ c₂≈c₃) ≡-refl (≈ˢ-trans p≈ˢq q≈ˢr)

data Degree : Set where
  -∞ : Degree
  ⟨_⟩ : ℕ → Degree

instance
  Degree-number : Number Degree
  Degree-number = record
    { Constraint = λ _ → ⊤
    ; fromNat = λ n → ⟨ n ⟩
    }

_⊔_ : Degree → Degree → Degree
-∞ ⊔ d₂ = d₂
⟨ d₁ ⟩ ⊔ -∞ = ⟨ d₁ ⟩
⟨ d₁ ⟩ ⊔ ⟨ d₂ ⟩ = ⟨ d₁ ⊔ℕ d₂ ⟩

degreeˢ : Spine → ℕ
degreeˢ (K c) = 0
degreeˢ (c +x^ n ∙ p) = ⟅ n ⇓⟆ +ℕ degreeˢ p

degree : Polynomial → Degree
degree 0ᵖ = -∞
degree (x^ n ∙ p) = ⟨ n +ℕ degreeˢ p ⟩

deg : ∀ p {p≉0 : p ≉ᵖ 0ᵖ} → ℕ
deg 0ᵖ {p≉0} = contradiction ≈ᵖ-refl p≉0
deg (x^ n ∙ p) {p≉0} = n +ℕ degreeˢ p

+ᵖ-*ᵖ-rawRing : RawRing (c ⊔ˡ ℓ) (c ⊔ˡ ℓ)
+ᵖ-*ᵖ-rawRing = record
  { Carrier = Polynomial
  ; _≈_ = _≈ᵖ_
  ; _+_ = _+ᵖ_
  ; _*_ = _*ᵖ_
  ; -_ = -ᵖ_
  ; 0# = 0ᵖ
  ; 1# = 1ᵖ
  }

open import Data.String using (String; _++_)
open import Data.Nat.Show using () renaming (show to show-ℕ)

show-Polynomial : (C → String) → Polynomial → String
show-Polynomial show-c 0ᵖ = "0"
show-Polynomial show-c (x^ n ∙ p) = loop n p
  where
  loop : ℕ → Spine → String
  loop zero (K c) = show-c (proj₁ c)
  loop zero (c +x^ n ∙ p) = show-c (proj₁ c) ++ " + " ++ loop ⟅ n ⇓⟆ p
  loop (suc n) (K c) = show-c (proj₁ c) ++ " * X^" ++ show-ℕ (suc n)
  loop (suc n) (c +x^ m ∙ p) = show-c (proj₁ c) ++ " * X^" ++ show-ℕ (suc n) ++ " + " ++ loop (suc n +ℕ ⟅ m ⇓⟆) p
