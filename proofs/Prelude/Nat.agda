open import Function using (_$_)
open import Relation.Nullary using (¬_; Dec)
open Dec
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (False)
open import Relation.Binary using (Reflexive; Transitive; Trans; Antisymmetric; Asymmetric; Irreflexive; Decidable; IsPreorder; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; resp₂; module ≡-Reasoning)
  renaming (isEquivalence to ≡-isEquivalence)
open import Relation.Binary.PropositionalEquality.WithK using (≡-erase)

open import Data.Unit using (tt)
open import Data.List using (List)
open List
open import Polynomial.Simple.AlmostCommutativeRing using (AlmostCommutativeRing)
open import Polynomial.Simple.AlmostCommutativeRing.Instances using (module Nat)
open import Polynomial.Simple.Reflection using (solveOver)
open Nat.Reflection using (∀⟨_⟩)

module Prelude.Nat where

open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≟_) public
open ℕ public
open import Data.Nat.DivMod using (_/_; _%_; m≡m%n+[m/n]*n )
open import Data.Nat.Properties using (+-assoc; +-suc; +-comm; *-identityʳ; +-identityʳ; m+n≡0⇒m≡0; +-cancelʳ-≡; +-cancelˡ-≡; 1+n≢0)
open import Data.Nat.Properties using (n∸n≡0; ∸-+-assoc; *-comm)

infix 4 _≤_
record _≤_ (n : ℕ) (m : ℕ) : Set where
  constructor lte
  field
    k : ℕ
    ≤-proof : n + k ≡ m

0≤n : ∀ {n} → 0 ≤ n
0≤n {n} = lte n refl

≤-refl : Reflexive _≤_
≤-refl {x} = lte 0 (≡-erase ∀⟨ x ∷ [] ⟩)

≤-trans : Transitive _≤_
≤-trans {x} (lte k₁ refl) (lte k₂ refl) = lte (k₁ + k₂) (≡-erase ∀⟨ x ∷ k₁ ∷ k₂ ∷ [] ⟩)

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
 { isEquivalence = ≡-isEquivalence
 ; reflexive = λ { refl → ≤-refl }
 ; trans = ≤-trans
 }

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

m≤m+n : ∀ {m n} → m ≤ m + n
m≤m+n {m} {n} = lte n refl

≤-erase : ∀ {n m} → n ≤ m → n ≤ m
≤-erase (lte k ≤-proof) = lte k (≡-erase ≤-proof)

infix 4 _<_ _≮_
_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

_≮_ : ℕ → ℕ → Set
n ≮ m = ¬ (n < m)

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

n<1+n : ∀ {n} → n < 1 + n
n<1+n = ≤-refl

0<1+n : ∀ {n} → 0 < 1 + n
0<1+n {n} = lte n refl

n≮0 : ∀ {n} → n ≮ 0
n≮0 ()

private
  a+b∸a≡b+[a∸a] : ∀ a b → a + b ∸ a ≡ b + (a ∸ a)
  a+b∸a≡b+[a∸a] zero b = sym (+-identityʳ b)
  a+b∸a≡b+[a∸a] (suc a) b = a+b∸a≡b+[a∸a] a b

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

*-mono-< : _*_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
*-mono-< {x} {_} {u} (lte k refl) (lte m refl) =
  lte (k * m + k * u + k + m * x + m + u + x) (≡-erase ∀⟨ x ∷ u ∷ k ∷ m ∷ [] ⟩)

*-mono-≤ : _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
*-mono-≤ {x} {_} {u} (lte k refl) (lte m refl) = lte (k * m + k * u + m * x) (≡-erase ∀⟨ x ∷ u ∷ k ∷ m ∷ [] ⟩)

<⇒≤ : ∀ {n m} → n < m → n ≤ m
<⇒≤ {n} (lte k refl) = lte (suc k) (≡-erase (+-suc n k))

module ≤-Reasoning where
   open import Relation.Binary.Reasoning.Base.Triple
     ≤-isPreorder <-trans (resp₂ _<_) <⇒≤ <-≤-trans ≤-<-trans
     public hiding (_≈⟨_⟩_)

record Euclidean (n : ℕ) (m : ℕ) : Set where
  constructor Euclidean✓
  field
    q : ℕ
    r : ℕ
    division : n ≡ r + m * q
    r<m : r < m

open import Prelude.Unsafe using (TODO)

_div_ : ∀ n m {≢0 : False (m ≟ 0)} → Euclidean n m
n div suc m = Euclidean✓ (n / suc m) (n % suc m) (≡-erase div-proof) (lte (suc m ∸ suc (n % suc m)) (rem-proof n m))
  where
  div-proof : n ≡ n % suc m + suc m * (n / suc m)
  div-proof rewrite *-comm (suc m) (n / suc m) = m≡m%n+[m/n]*n n m
  rem-proof : ∀ x y → suc (x % suc y) + (suc y ∸ suc (x % suc y)) ≡ suc y
  rem-proof = TODO


-- _C_ : ℕ → ℕ → ℕ
-- n C zero = 1
-- zero C suc k = 0
-- suc n C suc k = n C k + n C (suc k)

-- _! : ℕ → ℕ
-- zero ! = 1
-- suc n ! = suc n * n !

-- 1≤n! : ∀ n → 1 ≤ n !
-- 1≤n! zero = ≤-refl
-- 1≤n! (suc n) = begin
--   1 ≤⟨ 1≤n! n ⟩
--   n ! ≤⟨ m≤m+n ⟩
--   n ! + n * n ! ≡⟨ refl ⟩
--   (1 + n) ! ∎
--   where
--   open ≤-Reasoning

-- n≤n! : ∀ n → n ≤ n !
-- n≤n! zero = 0≤n
-- n≤n! (suc n) = begin
--   suc n ≡⟨ sym (*-identityʳ (suc n)) ⟩
--   suc n * 1 ≤⟨ *-mono-≤ (≤-refl {suc n}) (1≤n! n) ⟩
--   (1 + n) ! ∎
--   where
--   open ≤-Reasoning

-- ≢⇒¬≟ : ∀ {n m} → n ≢ m → False (n ≟ m)
-- ≢⇒¬≟ {n} {m} n≢m with n ≟ m
-- ... | yes n≡m = contradiction n≡m n≢m
-- ... | no _ = tt

-- _C′_ : ℕ → ℕ → ℕ
-- n C′ k = (n ! / (k ! * (n ∸ k) !)) {≢⇒¬≟ den≢0}
--   where
--   den≢0 : k ! * (n ∸ k) ! ≢ 0
--   den≢0 den≡0 = <-irrefl (sym den≡0) (*-mono-< (1≤n! k) (1≤n! (n ∸ k)))

-- nC′0≡1 : ∀ {n} → n C′ 0 ≡ 1
-- nC′0≡1 {n} = lemma num≡dem
--   where
--   num≡dem : n ! ≡ (0 ! * (n ∸ 0) !)
--   num≡dem = sym (+-identityʳ (n !))
--   lemma : ∀ {num dem} .{dem≢0} → num ≡ dem → (num / dem) {dem≢0} ≡ 1
--   lemma {num} {_} {dem≢0} refl = n/n≡1 num {dem≢0}

-- -- 0C′n≡0 : ∀ {k} → 0 C′ k ≡ 0
-- -- 0C′n≡0 {k} = {!0/n≡0 (k ! * (0 ∸ k) !) {?}!}

-- -- lem : ∀ {n k} → n C k ≡ n C′ k
-- -- lem {n} {zero} = sym (nC′0≡1 {n})
-- -- lem {zero} {suc k} = {!refl!}
-- -- lem {suc n} {suc k} with lem {n} {k} | lem {n} {suc k}
-- -- ... | p₁ | p₂ = {!!}
