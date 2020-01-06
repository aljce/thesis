open import Level using () renaming (_⊔_ to _⊔ˡ_)

open import Data.Product using (_,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (yes; no)
open import Relation.Binary using (IsEquivalence; Tri)
open Tri
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Algebra.Bundles using (RawRing)
open import AKS.Algebra.Bundles using (DecField)

module AKS.Polynomial.Base {c ℓ} (F : DecField c ℓ)  where

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.FromNat using (Number)
open import AKS.Nat using (ℕ; _∸_; _<_; lte) renaming (_+_ to _+ℕ_; _⊔_ to _⊔ℕ_)
open ℕ
open import AKS.Nat using (≢⇒¬≟; <-cmp; suc-injective-≤; <-irrefl)
open import AKS.Nat using (ℕ⁺; ⟅_⇓⟆; ⟅_⇑⟆)

open DecField F
  using (0#; 1#; _+_; _*_; -_; _-_; _⁻¹; _/_; C/0)
  renaming (Carrier to C)
open DecField F using (_≈_; _≈?_; isEquivalence)
open IsEquivalence isEquivalence using ()
  renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open DecField F
  using (*-commutativeMonoid; 1#≉0#; -1#≉0#; _*/0_)
open import AKS.Exponentiation *-commutativeMonoid using (_^_; _^⁺_)

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
1ᵖ = x^ 0 ∙ K (1# , 1#≉0#)

_+?_ : ∀ (k₁ k₂ : C/0) → (proj₁ k₁ + proj₁ k₂ ≈ 0#) ⊎ C/0
k₁ +? k₂ with proj₁ k₁ + proj₁ k₂ ≈? 0#
... | yes k₁+k₂≈0 = inj₁ k₁+k₂≈0
... | no  k₁+k₂≉0 = inj₂ (proj₁ k₁ + proj₁ k₂ , k₁+k₂≉0)

+-spine-≡-K : ℕ → C/0 → Spine → Polynomial
+-spine-≡-K n c₁ (K c₂) with c₁ +? c₂
... | inj₁ _ = 0ᵖ
... | inj₂ c₁+c₂ = x^ n ∙ K c₁+c₂
+-spine-≡-K n c₁ (c₂ +x^ i₂ ∙ q) with c₁ +? c₂
... | inj₁ _ = x^ (n +ℕ ⟅ i₂ ⇓⟆) ∙ q
... | inj₂ c₁+c₂ = x^ n ∙ (c₁+c₂ +x^ i₂ ∙ q)

+-spine-≡ : ℕ → Spine → Spine → Polynomial
+-spine-< : ℕ → Spine → ℕ⁺ → Spine → Polynomial
+-spine : ℕ → Spine → ℕ → Spine → Polynomial

+-spine-≡ n (K c₁) q = +-spine-≡-K n c₁ q
+-spine-≡ n (c₁ +x^ i₁ ∙ p) (K c₂) = +-spine-≡-K n c₂ (c₁ +x^ i₁ ∙ p)
+-spine-≡ n (c₁ +x^ i₁ ∙ p) (c₂ +x^ i₂ ∙ q) with c₁ +? c₂
... | inj₁ _ = +-spine (n +ℕ ⟅ i₁ ⇓⟆) p (n +ℕ ⟅ i₂ ⇓⟆) q
... | inj₂ c₁+c₂ with +-spine ⟅ i₁ ⇓⟆ p ⟅ i₂ ⇓⟆ q
...   | 0ᵖ = x^ n ∙ K c₁+c₂
...   | x^ zero ∙ r = +-spine-≡-K n c₁+c₂ r
...   | x^ suc n₃ ∙ r = x^ n ∙ (c₁+c₂ +x^ ⟅ suc n₃ ⇑⟆ ∙ r)

+-spine-< n₁ (K c₁) n₂ q = x^ n₁ ∙ (c₁ +x^ n₂ ∙ q)
+-spine-< n₁ (c₁ +x^ i₁ ∙ p) n₂ q with +-spine ⟅ i₁ ⇓⟆ p ⟅ n₂ ⇓⟆ q
... | 0ᵖ = x^ n₁ ∙ K c₁
... | x^ zero ∙ r = +-spine-≡-K n₁ c₁ r
... | x^ suc n₃ ∙ r = x^ n₁ ∙ (c₁ +x^ ⟅ suc n₃ ⇑⟆ ∙ r)

m<n⇒n∸m≢0 : ∀ {m n} → m < n → n ∸ m ≢ 0
m<n⇒n∸m≢0 {zero} {n} m<n n∸m≡0 = <-irrefl (sym n∸m≡0) m<n
m<n⇒n∸m≢0 {suc m} {suc n} m<n n∸m≡0 = m<n⇒n∸m≢0 (suc-injective-≤ m<n) n∸m≡0

+-spine n₁ p n₂ q with <-cmp n₁ n₂
+-spine n₁ p n₂ q | tri< n₁<n₂ _ _ = +-spine-< n₁ p (⟅ n₂ ∸ n₁ ⇑⟆ {≢⇒¬≟ (m<n⇒n∸m≢0 n₁<n₂)}) q
+-spine n₁ p n₂ q | tri≈ _ n₁≡n₂ _ = +-spine-≡ n₁ p q
+-spine n₁ p n₂ q | tri> _ _ n₁>n₂ = +-spine-< n₂ q (⟅ n₁ ∸ n₂ ⇑⟆ {≢⇒¬≟ (m<n⇒n∸m≢0 n₁>n₂)}) p

infixl 6 _+ᵖ_
_+ᵖ_ : Polynomial → Polynomial → Polynomial
0ᵖ +ᵖ q = q
(x^ n₁ ∙ p) +ᵖ 0ᵖ = x^ n₁ ∙ p
(x^ n₁ ∙ p) +ᵖ (x^ n₂ ∙ q) = +-spine n₁ p n₂ q

𝑋 : Polynomial
𝑋 = x^ 1 ∙ K (1# , 1#≉0#)

∙ᵖ-spine : C/0 → Spine → Spine
∙ᵖ-spine c₁ (K c₂) = K (c₁ */0 c₂)
∙ᵖ-spine c₁ (c₂ +x^ n ∙ p) = (c₁ */0 c₂) +x^ n ∙ (∙ᵖ-spine c₁ p)

infixl 7 _∙ᵖ_
_∙ᵖ_ : C/0 → Polynomial → Polynomial
c ∙ᵖ 0ᵖ = 0ᵖ
c ∙ᵖ (x^ n ∙ p) = x^ n ∙ (∙ᵖ-spine c p)

*ᵖ-spine : ℕ → Spine → ℕ → Spine → Polynomial
*ᵖ-spine o₁ (K c₁) o₂ q = x^ (o₁ +ℕ o₂) ∙ (∙ᵖ-spine c₁ q)
*ᵖ-spine o₁ (c₁ +x^ n₁ ∙ p) o₂ (K c₂) = x^ (o₁ +ℕ o₂) ∙ (∙ᵖ-spine c₂ (c₁ +x^ n₁ ∙ p))
*ᵖ-spine o₁ (c₁ +x^ n₁ ∙ p) o₂ (c₂ +x^ n₂ ∙ q) =
  x^ (o₁ +ℕ o₂) ∙ K (c₁ */0 c₂) +ᵖ
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
-ᵖ p = (- 1# , -1#≉0#) ∙ᵖ p

infix 4 _≈ᵖ_
record _≈ᵖ_ (p : Polynomial) (q : Polynomial) : Set (c ⊔ˡ ℓ) where
  constructor ≈✓
  field
    ∀x[pₓ≈qₓ] : ∀ x → ⟦ p ⟧ x ≈ ⟦ q ⟧ x

data _≈ˢ_ : Spine → Spine → Set (c ⊔ˡ ℓ) where
  K≈ : ∀ {c₁ c₂} → proj₁ c₁ ≈ proj₁ c₂ → K c₁ ≈ˢ K c₂
  +≈ : ∀ {c₁ c₂} {n₁ n₂} {p q} → proj₁ c₁ ≈ proj₁ c₂ → n₁ ≡ n₂ → p ≈ˢ q → (c₁ +x^ n₁ ∙ p) ≈ˢ (c₂ +x^ n₂ ∙ q)

infix 4 _≈ⁱ_
data _≈ⁱ_ : Polynomial → Polynomial → Set (c ⊔ˡ ℓ) where
  0ᵖ≈ : 0ᵖ ≈ⁱ 0ᵖ
  0ᵖ≉ : ∀ {o₁ o₂} {p q} → o₁ ≡ o₂ → p ≈ˢ q → x^ o₁ ∙ p ≈ⁱ x^ o₁ ∙ q

-- _≈ⁱ?_ : Decidable _≈ⁱ_
-- p ≈ⁱ? q = ?

-- lemma : ∀ {p q} → p ≈ᵖ q → p ≈ⁱ q
-- lemma {0ᵖ} {0ᵖ} p≈ᵖq = 0ᵖ≈
-- lemma {0ᵖ} {x^ o₂ ∙ q} (≈✓ ∀x[pₓ≈qₓ]) = {!!}
-- lemma {x^ o₁ ∙ p} {0ᵖ} p≈ᵖq = {!!}
-- lemma {x^ o₁ ∙ p} {x^ x ∙ x₁} (≈✓ ∀x[pₓ≈qₓ]) = {!!}

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

-- 1 + x + x^2
ex2 : Polynomial
ex2 = 1ᵖ +ᵖ 𝑋 +ᵖ 𝑋 *ᵖ 𝑋
