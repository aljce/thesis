open import Level using (_⊔_)
open import Function using (_$_)

open import Relation.Binary using (Reflexive; Transitive; Antisymmetric; _Respects₂_; _Respectsʳ_; _Respectsˡ_; Symmetric)

open import Algebra.Bundles using (Semiring)

module AKS.Algebra.Divisibility {c ℓ} (S : Semiring c ℓ) where

open Semiring S using (_+_; _*_; 0#; 1#) renaming (Carrier to C)
open Semiring S using (_≈_; setoid; refl; sym; trans)
open import Relation.Binary.Reasoning.Setoid setoid
open Semiring S using (+-congˡ; +-identityʳ)
open Semiring S using (*-assoc; *-identityˡ; *-identityʳ; *-congˡ; zeroˡ; zeroʳ)
open import Algebra.Core using (Op₂)
open import Algebra.Definitions _≈_ using (Commutative)

record _∣_ (d : C) (a : C) : Set (c ⊔ ℓ) where
  constructor divides
  field
    quotient : C
    equality : a ≈ (quotient * d)

∣-refl : Reflexive _∣_
∣-refl {x} = divides 1# (sym (*-identityˡ x))

∣-trans : Transitive _∣_
∣-trans {x} {y} {z} (divides q₁ y≈q₁*x) (divides q₂ z≈q₂*y) = divides (q₂ * q₁) $ begin
  z ≈⟨ z≈q₂*y ⟩
  q₂ * y ≈⟨ *-congˡ y≈q₁*x ⟩
  q₂ * (q₁ * x) ≈⟨ sym (*-assoc q₂ q₁ x) ⟩
  (q₂ * q₁) * x ∎

open import Data.Product using (_,_)

∣-respʳ : _∣_ Respectsʳ _≈_
∣-respʳ {y} {x₁} {x₂} x₁≈x₂ (divides q x₁≈q*y) = divides q $ begin
  x₂    ≈⟨ sym x₁≈x₂ ⟩
  x₁    ≈⟨ x₁≈q*y ⟩
  q * y ∎

∣-respˡ : _∣_ Respectsˡ _≈_
∣-respˡ {y} {x₁} {x₂} x₁≈x₂ (divides q y≈q*x₁) = divides q $ begin
  y      ≈⟨ y≈q*x₁ ⟩
  q * x₁ ≈⟨ *-congˡ x₁≈x₂ ⟩
  q * x₂ ∎

∣-resp : _∣_ Respects₂ _≈_
∣-resp = ∣-respʳ , ∣-respˡ

infix 10 1∣_ _∣0

1∣_ : ∀ n → 1# ∣ n
1∣ n = divides n (sym (*-identityʳ n))

_∣0 : ∀ n → n ∣ 0#
n ∣0 = divides 0# (sym (zeroˡ n))

0∣n⇒n≈0 : ∀ {n} → 0# ∣ n → n ≈ 0#
0∣n⇒n≈0 {n} (divides q n≈q*0) = begin
  n      ≈⟨ n≈q*0 ⟩
  q * 0# ≈⟨ zeroʳ q ⟩
  0#     ∎

-- ∣-antisym : Antisymmetric _≈_ _∣_
-- ∣-antisym {x} {y} (divides q₁ y≈q₁*x) (divides q₂ x≈q₂*y) = {!!}

record IsGCD (gcd : Op₂ C) : Set (c ⊔ ℓ) where
  field
    gcd[a,b]∣a : ∀ a b → gcd a b ∣ a
    gcd[a,b]∣b : ∀ a b → gcd a b ∣ b
    gcd-greatest : ∀ {c a b} → c ∣ a → c ∣ b → c ∣ gcd a b

module GCD {gcd : Op₂ C} (isGCD : IsGCD gcd) (∣-antisym : Antisymmetric _≈_ _∣_) where
  open IsGCD isGCD

  infix 4 _⊥_
  _⊥_ : C → C → Set ℓ
  n ⊥ m = gcd n m ≈ 1#

  gcd[0,0]≈0 : gcd 0# 0# ≈ 0#
  gcd[0,0]≈0 = ∣-antisym (gcd 0# 0# ∣0) (gcd-greatest ∣-refl ∣-refl)

  gcd-comm : Commutative gcd
  gcd-comm a b = ∣-antisym
    (gcd-greatest (gcd[a,b]∣b a b) (gcd[a,b]∣a a b))
    (gcd-greatest (gcd[a,b]∣b b a) (gcd[a,b]∣a b a))

  gcd[a,b]≈0⇒a≈0 : ∀ {a b} → gcd a b ≈ 0# → a ≈ 0#
  gcd[a,b]≈0⇒a≈0 {a} {b} gcd[a,b]≈0 = 0∣n⇒n≈0 (∣-respˡ gcd[a,b]≈0 (gcd[a,b]∣a a b))

  gcd[a,b]≈0⇒b≈0 : ∀ {a b} → gcd a b ≈ 0# → b ≈ 0#
  gcd[a,b]≈0⇒b≈0 {a} {b} gcd[a,b]≈0 = 0∣n⇒n≈0 (∣-respˡ gcd[a,b]≈0 (gcd[a,b]∣b a b))

  -- gcd[a,b]≢0 : ∀ a b → a ≉ 0 ⊎ b ≉ 0 → gcd a b ≉ 0
  -- gcd[a,b]≢0 a b e = ?

  data Identity (d : C) (a : C) (b : C) : Set (c ⊔ ℓ) where
    +ʳ : ∀ (x y : C) → d + x * a ≈ y * b → Identity d a b
    +ˡ : ∀ (x y : C) → d + y * b ≈ x * a → Identity d a b

  identity-sym : ∀ {d} → Symmetric (Identity d)
  identity-sym {d} {a} {b} (+ʳ x y d+x*a≈y*b) = +ˡ y x d+x*a≈y*b
  identity-sym {d} {a} {b} (+ˡ x y d+y*b≈x*a) = +ʳ y x d+y*b≈x*a

  identity-refl : ∀ {d} → Identity d d d
  identity-refl {d} = +ʳ 0# 1# $ begin
    d + 0# * d ≈⟨ +-congˡ (zeroˡ d) ⟩
    d + 0#     ≈⟨ +-identityʳ d ⟩
    d          ≈⟨ sym (*-identityˡ d) ⟩
    1# * d     ∎

  identity-base : ∀ {d} → Identity d d 0#
  identity-base {d} = +ˡ 1# 0# $ begin
    d + 0# * 0# ≈⟨ +-congˡ (zeroˡ 0#) ⟩
    d + 0#      ≈⟨ +-identityʳ d ⟩
    d           ≈⟨ sym (*-identityˡ d) ⟩
    1# * d      ∎

  data Bézout (a : C) (b : C) : Set (c ⊔ ℓ) where
    lemma : ∀ d → gcd a b ≈ d → Identity d a b → Bézout a b

