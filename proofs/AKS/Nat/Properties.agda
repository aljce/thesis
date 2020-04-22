open import Level using (0ℓ)
open import Function using (_$_; _∘_)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (False)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
  using (Reflexive; Transitive; Trans; Antisymmetric; Asymmetric; Irreflexive; Decidable; Total; IsPreorder; IsPartialOrder; IsTotalOrder; TotalOrder; _Preserves₂_⟶_⟶_; Trichotomous; Tri; Irrelevant; Connex)
open Tri
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; resp₂; module ≡-Reasoning)
  renaming (isEquivalence to ≡-isEquivalence)
open import Relation.Binary.PropositionalEquality.WithK using (≡-erase)

open import Data.Bool using (T)
open import Data.Bool.Properties using (T?)
open import Data.Unit using (tt)

open import Data.List using (List)
open List
open import Data.Sum using (_⊎_)
open _⊎_

module AKS.Nat.Properties where

open import Data.Nat.Properties using (+-assoc; +-suc; +-comm; *-identityʳ; +-identityʳ; m+n≡0⇒m≡0; +-cancelʳ-≡; +-cancelˡ-≡; 1+n≢0; suc-injective) public
open import Data.Nat.Properties using (n∸n≡0; ∸-+-assoc) public
open import Data.Nat.Properties using (*-comm; *-1-commutativeMonoid) public

open import Polynomial.Simple.AlmostCommutativeRing using (AlmostCommutativeRing)
open import Polynomial.Simple.AlmostCommutativeRing.Instances using (module Nat)
open import Polynomial.Simple.Reflection using (solveOver)
open Nat.Reflection using (∀⟨_⟩)

open import AKS.Nat.Base using (ℕ; _+_; _*_; _∸_; lte; _≤_; _≥_; _≰_; _≱_; _<_; _≮_; _>_; _≯_; _<ᵇ_; _≟_; ℕ⁺; ℕ+; ⟅_⇓⟆; ⟅_⇑⟆; pred)
open ℕ
open import Algebra.Definitions {A = ℕ} _≡_ using (_DistributesOverˡ_)

≢⇒¬≟ : ∀ {n m} → n ≢ m → False (n ≟ m)
≢⇒¬≟ {n} {m} n≢m with n ≟ m
... | yes n≡m = contradiction n≡m n≢m
... | no _ = tt

¬≟⇒≢ : ∀ {n m} → False (n ≟ m) → n ≢ m
¬≟⇒≢ {n} {m} ¬n≟m n≡m with n ≟ m
... | no n≢m = contradiction n≡m n≢m

ℕ→ℕ⁺→ℕ : ∀ n {n≢0} → ⟅ ⟅ n ⇑⟆ {n≢0} ⇓⟆ ≡ n
ℕ→ℕ⁺→ℕ (suc n) {n≢0} = refl

⟅⇓⟆-injective : ∀ {n m} → pred ⟅ n ⇓⟆ ≡ pred ⟅ m ⇓⟆ → n ≡ m
⟅⇓⟆-injective {ℕ+ n} {ℕ+ m} refl = refl

n≢0∧m≢0⇒n*m≢0 : ∀ {n m} → n ≢ 0 → m ≢ 0 → n * m ≢ 0
n≢0∧m≢0⇒n*m≢0 {zero} {m} n≢0 m≢0 = contradiction refl n≢0
n≢0∧m≢0⇒n*m≢0 {suc n} {zero} n≢0 m≢0 = contradiction refl m≢0
n≢0∧m≢0⇒n*m≢0 {suc n} {suc m} n≢0 m≢0 ()

------------ _≤_ --------------

0≤n : ∀ {n} → 0 ≤ n
0≤n {n} = lte n refl

≤-refl : Reflexive _≤_
≤-refl {x} = lte 0 (≡-erase ∀⟨ x ∷ [] ⟩)

≤-reflexive : ∀ {n m} → n ≡ m → n ≤ m
≤-reflexive refl = ≤-refl

≤-trans : Transitive _≤_
≤-trans {x} (lte k₁ refl) (lte k₂ refl) = lte (k₁ + k₂) (≡-erase ∀⟨ x ∷ k₁ ∷ k₂ ∷ [] ⟩)

n+m≡n⇒m≡0 : ∀ {n m} → n + m ≡ n → m ≡ 0
n+m≡n⇒m≡0 {n} {m} n+m≡n = m≡0
  where
  open ≡-Reasoning
  m≡0 : m ≡ 0
  m≡0 = +-cancelˡ-≡ n $ begin
    n + m ≡⟨ n+m≡n ⟩
    n ≡⟨ sym (+-identityʳ n) ⟩
    n + 0 ∎

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym {x} {y} (lte k₁ x+k₁≡y) (lte k₂ y+k₂≡x) = ≡-erase (+-cancelʳ-≡ x y x+k₁≡y+k₁)
  where
  open ≡-Reasoning

  k₁+k₂≡0 : k₁ + k₂ ≡ 0
  k₁+k₂≡0 = n+m≡n⇒m≡0 $ begin
    x + (k₁ + k₂) ≡⟨ sym (+-assoc x k₁ k₂) ⟩
    (x + k₁) + k₂ ≡⟨ cong (λ t → t + k₂) x+k₁≡y ⟩
    y + k₂ ≡⟨ y+k₂≡x ⟩
    x ∎

  x+k₁≡y+k₁ : x + k₁ ≡ y + k₁
  x+k₁≡y+k₁ = begin
    x + k₁ ≡⟨ x+k₁≡y ⟩
    y      ≡⟨ sym (+-identityʳ y) ⟩
    y + 0  ≡⟨ cong (λ t → y + t) (sym (m+n≡0⇒m≡0 k₁ k₁+k₂≡0)) ⟩
    y + k₁ ∎

suc-mono-≤ : ∀ {n m} → n ≤ m → suc n ≤ suc m
suc-mono-≤ (lte k₁ refl) = lte k₁ refl

suc-injective-≤ : ∀ {n m} → suc n ≤ suc m → n ≤ m
suc-injective-≤ (lte k refl) = lte k refl

m≤m+n : ∀ {m n} → m ≤ m + n
m≤m+n {m} {n} = lte n refl

m≤n+m : ∀ {m n} → m ≤ n + m
m≤n+m {m} {n} = lte n (+-comm m n)

≤-erase : ∀ {n m} → n ≤ m → n ≤ m
≤-erase (lte k ≤-proof) = lte k (≡-erase ≤-proof)

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
 { isEquivalence = ≡-isEquivalence
 ; reflexive = ≤-reflexive
 ; trans = ≤-trans
 }

≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

------------ _<_ --------------

<-trans : Transitive _<_
<-trans {x} (lte k₁ refl) (lte k₂ refl) = lte (suc (k₁ + k₂)) (≡-erase ∀⟨ x ∷ k₁ ∷ k₂ ∷ [] ⟩)

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans x<y y≤z = ≤-trans x<y y≤z

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans {x} (lte k₁ refl) (lte k₂ refl) = lte (k₁ + k₂) (≡-erase ∀⟨ x ∷ k₁ ∷ k₂ ∷ [] ⟩)

n≮n : ∀ {n} → n ≮ n
n≮n {n} (lte k n+1+k≡n) rewrite sym (+-suc n k) = 1+n≢0 (n+m≡n⇒m≡0 n+1+k≡n)

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl x<x = n≮n x<x

<-asym : Asymmetric _<_
<-asym x<y y<x = n≮n (<-trans x<y y<x)

<⇒≯ : ∀ {n m} → n < m → n ≯ m
<⇒≯ n<m n>m = <-asym n<m n>m

n<1+n : ∀ {n} → n < 1 + n
n<1+n = ≤-refl

0<1+n : ∀ {n} → 0 < 1 + n
0<1+n {n} = lte n refl

n≮0 : ∀ {n} → n ≮ 0
n≮0 ()

suc-mono-< : ∀ {n m} → n < m → suc n < suc m
suc-mono-< (lte k₁ refl) = lte k₁ refl

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {x} {_} {u} (lte k refl) (lte m refl) = lte (k + m) (≡-erase (solveOver (x ∷ u ∷ k ∷ m ∷ []) Nat.ring))

+-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
+-mono-< {x} {_} {u} (lte k refl) (lte m refl) = lte (suc (k + m)) (≡-erase (solveOver (x ∷ u ∷ k ∷ m ∷ []) Nat.ring))

private
  a+b∸a≡b+[a∸a] : ∀ a b → a + b ∸ a ≡ b + (a ∸ a)
  a+b∸a≡b+[a∸a] zero b = sym (+-identityʳ b)
  a+b∸a≡b+[a∸a] (suc a) b = a+b∸a≡b+[a∸a] a b

m+[n∸m]≡n : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
m+[n∸m]≡n {m} {n} (lte k refl) = begin
  m + (m + k ∸ m)   ≡⟨ cong (λ x → m + x) (a+b∸a≡b+[a∸a] m k) ⟩
  m + (k + (m ∸ m)) ≡⟨ cong (λ x → m + (k + x)) (n∸n≡0 m) ⟩
  m + (k + 0)       ≡⟨ cong (λ x → m + x) (+-identityʳ k) ⟩
  m + k ∎
  where
  open ≡-Reasoning

[n∸m]+m≡n : ∀ {m n} → m ≤ n → (n ∸ m) + m ≡ n
[n∸m]+m≡n {m} {n} rewrite +-comm (n ∸ m) m = m+[n∸m]≡n

m<n⇒n∸m≢0 : ∀ {m n} → m < n → n ∸ m ≢ 0
m<n⇒n∸m≢0 {zero} {n} m<n n∸m≡0 = <-irrefl (sym n∸m≡0) m<n
m<n⇒n∸m≢0 {suc m} {suc n} m<n n∸m≡0 = m<n⇒n∸m≢0 (suc-injective-≤ m<n) n∸m≡0

∸-mono-<ˡ : ∀ {x b t} → x ≤ b → b < t → b ∸ x < t ∸ x
∸-mono-<ˡ {x} (lte k₁ refl) (lte k₂ refl) = lte k₂ (≡-erase ≤-proof)
  where
  open ≡-Reasoning
  lemma₁ : ∀ a → 1 + (k₁ + a) + k₂ ≡ 1 + k₁ + k₂ + a
  lemma₁ a = ∀⟨ a ∷ k₁ ∷ k₂ ∷ [] ⟩
  lemma₂ : x + (1 + k₁ + k₂) ≡ 1 + (x + k₁ + k₂)
  lemma₂ = ∀⟨ x ∷ k₁ ∷ k₂ ∷ [] ⟩
  ≤-proof : suc (x + k₁ ∸ x) + k₂ ≡ suc (x + k₁) + k₂ ∸ x
  ≤-proof = begin
    suc (x + k₁ ∸ x) + k₂ ≡⟨ cong (λ t → suc t + k₂) (a+b∸a≡b+[a∸a] x k₁) ⟩
    suc (k₁ + (x ∸ x)) + k₂ ≡⟨ lemma₁ (x ∸ x) ⟩
    suc k₁ + k₂ + (x ∸ x) ≡⟨ sym (a+b∸a≡b+[a∸a] x (suc k₁ + k₂)) ⟩
    x + (suc k₁ + k₂) ∸ x ≡⟨ cong (λ t → t ∸ x) lemma₂ ⟩
    suc (x + k₁) + k₂ ∸ x ∎

∸-mono-<ʳ : ∀ {x b t} → t ≤ x → b < t → x ∸ t < x ∸ b
∸-mono-<ʳ {b = b} (lte k₁ refl) (lte k₂ refl) = lte k₂ (≡-erase ≤-proof)
  where
  open ≡-Reasoning
  LHS : suc (suc b + k₂ + k₁ ∸ (suc b + k₂) + k₂) ≡ suc (k₂ + k₁)
  LHS = cong suc $ begin
    suc b + k₂ + k₁ ∸ (suc b + k₂) + k₂ ≡⟨ cong (λ t → t + k₂) (sym (∸-+-assoc (b + k₂ + k₁) b k₂)) ⟩
    suc b + k₂ + k₁ ∸ suc b ∸ k₂ + k₂ ≡⟨ cong (λ t → t ∸ suc b ∸ k₂ + k₂) (+-assoc (suc b) k₂ k₁) ⟩
    suc b + (k₂ + k₁) ∸ suc b ∸ k₂ + k₂ ≡⟨ cong (λ t →  t ∸ k₂ + k₂) (a+b∸a≡b+[a∸a] (suc b) (k₂ + k₁)) ⟩
    k₂ + k₁ + (suc b ∸ suc b) ∸ k₂ + k₂ ≡⟨ cong (λ t → k₂ + k₁ + t ∸ k₂ + k₂) (n∸n≡0 (suc b)) ⟩
    k₂ + k₁ + 0 ∸ k₂ + k₂ ≡⟨  cong (λ t → t ∸ k₂ + k₂) (+-identityʳ (k₂ + k₁)) ⟩
    k₂ + k₁ ∸ k₂ + k₂ ≡⟨ cong (λ t → t + k₂) (a+b∸a≡b+[a∸a] k₂ k₁) ⟩
    k₁ + (k₂ ∸ k₂) + k₂ ≡⟨ cong (λ t → k₁ + t + k₂) (n∸n≡0 k₂) ⟩
    k₁ + 0 + k₂ ≡⟨ cong (λ t → t + k₂) (+-identityʳ k₁) ⟩
    k₁ + k₂ ≡⟨ +-comm k₁ k₂ ⟩
    k₂ + k₁ ∎
  lemma₁ : 1 + (b + k₂ + k₁) ≡ b + (1 + (k₂ + k₁))
  lemma₁ = ∀⟨ b ∷ k₂ ∷ k₁ ∷ [] ⟩
  RHS : suc (b + k₂ + k₁) ∸ b ≡ suc (k₂ + k₁)
  RHS = begin
    suc (b + k₂ + k₁) ∸ b ≡⟨ cong (λ t → t ∸ b) lemma₁ ⟩
    b + suc (k₂ + k₁) ∸ b ≡⟨ a+b∸a≡b+[a∸a] b (suc (k₂ + k₁)) ⟩
    suc (k₂ + k₁) + (b ∸ b) ≡⟨ cong (λ t → suc (k₂ + k₁) + t) (n∸n≡0 b) ⟩
    suc (k₂ + k₁) + 0 ≡⟨ +-identityʳ (suc (k₂ + k₁)) ⟩
    suc (k₂ + k₁) ∎
  ≤-proof : suc (suc b + k₂ + k₁ ∸ (suc b + k₂) + k₂) ≡ suc (b + k₂ + k₁) ∸ b
  ≤-proof = trans LHS (sym RHS)

∸-mono-≤ˡ : ∀ {x b t} → x ≤ b → b ≤ t → b ∸ x ≤ t ∸ x
∸-mono-≤ˡ {x} {b} {t} (lte k₁ refl) (lte k₂ refl) = lte k₂ ≤-proof
  where
  open ≡-Reasoning
  lemma₁ : ∀ a → k₁ + a + k₂ ≡ k₁ + k₂ + a
  lemma₁ a = ∀⟨ a ∷ k₁ ∷ k₂ ∷ [] ⟩
  ≤-proof : x + k₁ ∸ x + k₂ ≡ x + k₁ + k₂ ∸ x
  ≤-proof = begin
    x + k₁ ∸ x + k₂   ≡⟨ cong (λ t → t + k₂) (a+b∸a≡b+[a∸a] x k₁) ⟩
    k₁ + (x ∸ x) + k₂ ≡⟨ lemma₁ (x ∸ x) ⟩
    k₁ + k₂ + (x ∸ x) ≡⟨ sym (a+b∸a≡b+[a∸a] x (k₁ + k₂)) ⟩
    x + (k₁ + k₂) ∸ x ≡⟨ cong (λ t → t ∸ x) (sym (+-assoc x k₁ k₂)) ⟩
    x + k₁ + k₂ ∸ x   ∎

*-mono-< : _*_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
*-mono-< {x} {_} {u} (lte k refl) (lte m refl) =
  lte (k * m + k * u + k + m * x + m + u + x) (≡-erase ∀⟨ x ∷ u ∷ k ∷ m ∷ [] ⟩)

*-mono-≤ : _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
*-mono-≤ {x} {_} {u} (lte k refl) (lte m refl) = lte (k * m + k * u + m * x) (≡-erase ∀⟨ x ∷ u ∷ k ∷ m ∷ [] ⟩)

+-lower-≤ : ∀ x {n m} → n + x ≤ m → n ≤ m
+-lower-≤ x {n} {m} (lte q refl) = lte (x + q) (sym (+-assoc n x q))

<⇒≤ : ∀ {n m} → n < m → n ≤ m
<⇒≤ {n} (lte k refl) = lte (suc k) (≡-erase (+-suc n k))

module ≤-Reasoning where
   open import Relation.Binary.Reasoning.Base.Triple
     ≤-isPreorder <-trans (resp₂ _<_) <⇒≤ <-≤-trans ≤-<-trans
     public

n≤m⇒n<m⊎n≡m : ∀ {n m} → n ≤ m → n < m ⊎ n ≡ m
n≤m⇒n<m⊎n≡m {n} (lte zero ≤-proof) rewrite ≡-erase (+-identityʳ n) = inj₂ ≤-proof
n≤m⇒n<m⊎n≡m {n} (lte (suc k) ≤-proof) rewrite ≡-erase (+-suc n k) = inj₁ (lte k ≤-proof)

≤∧≢⇒< : ∀ {m n} → m ≤ n → m ≢ n → m < n
≤∧≢⇒< m≤n m≢n with n≤m⇒n<m⊎n≡m m≤n
... | inj₁ m<n = m<n
... | inj₂ m≡n = contradiction m≡n m≢n

≮⇒≥ : ∀ {m n} → m ≮ n → m ≥ n
≮⇒≥ {_} {zero} m≮n = 0≤n
≮⇒≥ {zero} {suc n} m≮n = contradiction 0<1+n m≮n
≮⇒≥ {suc m} {suc n} m≮n = suc-mono-≤ (≮⇒≥ (m≮n ∘ suc-mono-<))

<⇒≱ : ∀ {m n} → m < n → m ≱ n
<⇒≱ {m} {n} m<n m≥n with n≤m⇒n<m⊎n≡m m≥n
... | inj₁ m>n = <-asym m<n m>n
... | inj₂ m≡n = <-irrefl (sym m≡n) m<n

<ᵇ⇒< : ∀ m n → T (m <ᵇ n) → m < n
<ᵇ⇒< zero    (suc n) m<n = 0<1+n
<ᵇ⇒< (suc m) (suc n) m<n = suc-mono-< (<ᵇ⇒< m n m<n)

<⇒<ᵇ : ∀ m n → m < n → T (m <ᵇ n)
<⇒<ᵇ zero (suc n) m<n = tt
<⇒<ᵇ (suc m) (suc n) m<n = <⇒<ᵇ m n (suc-injective-≤ m<n)

0≢⇒0< : ∀ {n} → 0 ≢ n → 0 < n
0≢⇒0< {zero} 0≢n = contradiction refl 0≢n
0≢⇒0< {suc n} 0≢n = 0<1+n

-- TODO change to does/proof
<-cmp : Trichotomous _≡_ _<_
<-cmp m n with m ≟ n | T? (m <ᵇ n)
... | yes m≡n | _       = tri≈ (<-irrefl m≡n) m≡n (<-irrefl (sym m≡n))
... | no  m≢n | yes m<n = tri< (<ᵇ⇒< m n m<n) m≢n (<⇒≯ (<ᵇ⇒< m n m<n))
... | no  m≢n | no  m≮n = tri> (m≮n ∘ <⇒<ᵇ m n) m≢n (≤∧≢⇒< (≮⇒≥ (m≮n ∘ <⇒<ᵇ m n)) (m≢n ∘ sym))

<-≤-connex : Connex _<_ _≤_
<-≤-connex m n with <-cmp m n
... | tri< n<m _ _  = inj₁ n<m
... | tri≈ _ refl _ = inj₂ ≤-refl
... | tri> _ _ n>m  = inj₂ (<⇒≤ n>m)

<-irrelevant : Irrelevant _<_
<-irrelevant {x} (lte k₁ 1+x+k₁≡y) (lte k₂ 1+x+k₂≡y) with +-cancelˡ-≡ (1 + x) (trans 1+x+k₁≡y (sym 1+x+k₂≡y))
<-irrelevant {x} (lte k₁ refl) (lte .k₁ refl) | refl = refl

≤-total : Total _≤_
≤-total n m with <-cmp n m
... | tri< n<m _ _  = inj₁ (<⇒≤ n<m)
... | tri≈ _ refl _ = inj₁ ≤-refl
... | tri> _ _ n>m  = inj₂ (<⇒≤ n>m)

≤-isTotalOrder : IsTotalOrder _≡_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

≤-totalOrder : TotalOrder 0ℓ 0ℓ 0ℓ
≤-totalOrder = record { isTotalOrder = ≤-isTotalOrder }

open import Algebra.Construct.NaturalChoice.Max ≤-totalOrder public

+-distribˡ-⊔ : _+_ DistributesOverˡ _⊔_
+-distribˡ-⊔ x y z with ≤-total z y
+-distribˡ-⊔ x y z | inj₁ z≤y with ≤-total (x + z) (x + y)
+-distribˡ-⊔ x y z | inj₁ z≤y | inj₁ x+z≤x+y = refl
+-distribˡ-⊔ x y z | inj₁ z≤y | inj₂ x+y≤x+z = ≤-antisym x+y≤x+z (+-mono-≤ ≤-refl z≤y)
+-distribˡ-⊔ x y z | inj₂ y≤z with ≤-total (x + z) (x + y)
+-distribˡ-⊔ x y z | inj₂ y≤z | inj₁ x+z≤x+y = ≤-antisym x+z≤x+y (+-mono-≤ ≤-refl y≤z)
+-distribˡ-⊔ x y z | inj₂ y≤z | inj₂ x+y≤x+z = refl

⊔-least-≤ : ∀ n m o → n ≤ o → m ≤ o → n ⊔ m ≤ o
⊔-least-≤ n m o n≤o m≤o with ≤-total m n
... | inj₁ _ = n≤o
... | inj₂ _ = m≤o

⊔-least-< : ∀ n m o → n < o → m < o → n ⊔ m < o
⊔-least-< n m o n<o m<o with ≤-total m n
... | inj₁ _ = n<o
... | inj₂ _ = m<o

m≤n⇒m⊔n≡n : ∀ {m n} → m ≤ n → m ⊔ n ≡ n
m≤n⇒m⊔n≡n {m} {n} m≤n with ≤-total n m
... | inj₁ n≤m = ≤-antisym m≤n n≤m
... | inj₂ _   = refl


