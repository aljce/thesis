open import Level using (_⊔_; suc; Lift; lift)
open import Function using (_$_; _∘_; _⤖_)
open import Relation.Nullary.Decidable using (False)
open import Relation.Binary using (Rel; Decidable; Setoid; DecSetoid; IsEquivalence; IsDecEquivalence)

open import Data.Empty using (⊥)
open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_)

module AKS.Algebra.Structures {c ℓ} (C : Set c) (_≈_ : Rel C ℓ) where

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.FromNat using (Number)
open import AKS.Nat using (ℕ; _<_; _≟_)
open import AKS.Fin using (Fin)

open import Algebra.FunctionProperties using (Op₂; Op₁)
open import Algebra.Structures _≈_ using (IsCommutativeRing; IsAbelianGroup)

infix 4 _≉_
_≉_ : Rel C ℓ
x ≉ y = x ≈ y → ⊥

record IsNonZeroCommutativeRing (_+_ _*_ : Op₂ C) (-_ : Op₁ C) (0# 1# : C) : Set (c ⊔ ℓ) where
  field
    isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0# 1#
    0#≉1# : 0# ≉ 1#

  open IsCommutativeRing isCommutativeRing public
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Algebra.Properties.Ring (record { isRing = isRing }) using (-‿distribˡ-*; -‿involutive)

  1#≉0# : 1# ≉ 0#
  1#≉0# = 0#≉1# ∘ sym

  0#≉-1# : 0# ≉ - 1#
  0#≉-1# 0#≈-1# = 0#≉1# $ begin
    0#              ≈⟨ sym (zeroʳ 0#) ⟩
    0# * 0#         ≈⟨ *-cong 0#≈-1# 0#≈-1# ⟩
    (- 1#) * (- 1#) ≈⟨ sym (-‿distribˡ-* 1# (- 1#)) ⟩
    - (1# * (- 1#)) ≈⟨ -‿cong (*-identityˡ (- 1#)) ⟩
    - (- 1#)        ≈⟨ -‿involutive 1# ⟩
    1#              ∎

  -1#≉0# : - 1# ≉ 0#
  -1#≉0# = 0#≉-1# ∘ sym

  C/0 : Set (c ⊔ ℓ)
  C/0 = ∃[ x ] (x ≉ 0#)

  1#-nonzero : C/0
  1#-nonzero = 1# , 1#≉0#

  -1#-nonzero : C/0
  -1#-nonzero = - 1# , -1#≉0#

  fromNat : ℕ → C
  fromNat ℕ.zero = 0#
  fromNat (ℕ.suc ℕ.zero) = 1#
  fromNat (ℕ.suc (ℕ.suc n)) = 1# + fromNat (ℕ.suc n)

  instance
    C-number : Number C
    C-number = record
      { Constraint = λ _ → Lift c ⊤
      ; fromNat = λ n → fromNat n
      }

record IsIntegralDomain (_+_ _*_ : Op₂ C) (-_ : Op₁ C) (0# 1# : C) : Set (c ⊔ ℓ) where
  field
    isNonZeroCommutativeRing : IsNonZeroCommutativeRing _+_ _*_ -_ 0# 1#
    *-cancelˡ : ∀ x {y z} → x ≉ 0# → (x * y) ≈ (x * z) → y ≈ z

  open IsNonZeroCommutativeRing isNonZeroCommutativeRing public
  open import Relation.Binary.Reasoning.Setoid setoid

  *-cancelʳ : ∀ x {y z} → x ≉ 0# → (y * x) ≈ (z * x) → y ≈ z
  *-cancelʳ x {y} {z} x≉0 y*x≈z*x = *-cancelˡ x x≉0 $ begin
    (x * y) ≈⟨ *-comm x y ⟩
    (y * x) ≈⟨ y*x≈z*x ⟩
    (z * x) ≈⟨ *-comm z x ⟩
    (x * z) ∎

  *≉0 : ∀ {c₁ c₂} → c₁ ≉ 0# → c₂ ≉ 0# → c₁ * c₂ ≉ 0#
  *≉0 {c₁} {c₂} c₁≉0 c₂≉0 c₁*c₂≈0 = c₂≉0 $ *-cancelˡ c₁ c₁≉0 $ begin
     (c₁ * c₂) ≈⟨ c₁*c₂≈0 ⟩
     (0#)      ≈⟨ sym (zeroʳ c₁) ⟩
     (c₁ * 0#) ∎

  infixl 7 _*-nonzero_
  _*-nonzero_ : C/0 → C/0 → C/0
  (c₁ , c₁≉0) *-nonzero (c₂ , c₂≉0) = c₁ * c₂ , *≉0 c₁≉0 c₂≉0

module Divisibility (_*_ : Op₂ C) where
  infix 4 _∣_
  record _∣_ (d : C) (a : C) : Set (c ⊔ ℓ) where
    constructor divides
    field
      quotient : C
      equality : a ≈ (quotient * d)

  record IsGCD (gcd : Op₂ C) : Set (c ⊔ ℓ) where
    field
      gcd[a,b]∣a : ∀ a b → gcd a b ∣ a
      gcd[a,b]∣b : ∀ a b → gcd a b ∣ b
      gcd-greatest : ∀ {c a b} → c ∣ a → c ∣ b → c ∣ gcd a b

record IsGCDDomain (_+_ _*_ : Op₂ C) (-_ : Op₁ C) (0# 1# : C) (gcd : Op₂ C) : Set (c ⊔ ℓ) where
  open Divisibility _*_ public
  field
    isIntegralDomain : IsIntegralDomain _+_ _*_ -_ 0# 1#
    gcd-isGCD : IsGCD gcd

  open IsIntegralDomain isIntegralDomain public

record IsUniqueFactorizationDomain (_+_ _*_ : Op₂ C) (-_ : Op₁ C) (0# 1# : C) (gcd : Op₂ C) : Set (c ⊔ ℓ) where
  field
    isGCDDomain : IsGCDDomain _+_ _*_ -_ 0# 1# gcd
    -- TODO define factorization

  open IsGCDDomain isGCDDomain public

module Modulus
  (0# : C) (∣_∣ : ∀ n {n≉0 : n ≉ 0#} → ℕ) (_mod_ : ∀ (n m : C) {m≉0 : m ≉ 0#} → C)
  where
  data Remainder (n : C) (m : C) {m≉0 : m ≉ 0#} : Set (c ⊔ ℓ) where
    0≈ : (r≈0 : (n mod m) {m≉0} ≈ 0#) → Remainder n m
    0≉ : (r≉0 : (n mod m) {m≉0} ≉ 0#) → ∣ n mod m ∣ {r≉0} < ∣ m ∣ {m≉0} → Remainder n m

module _
  (_+_ _*_ : Op₂ C) (-_ : Op₁ C) (0# 1# : C) (∣_∣ : ∀ n {n≉0 : n ≉ 0#} → ℕ)
  (_div_ : ∀ (n m : C) {m≉0 : m ≉ 0#} → C) (_mod_ : ∀ (n m : C) {m≉0 : m ≉ 0#} → C)
  (gcd : Op₂ C)
  where

  record IsEuclideanDomain : Set (c ⊔ ℓ) where
    open Modulus 0# ∣_∣ _mod_ public
    field
      isUniqueFactorizationDomain : IsUniqueFactorizationDomain _+_ _*_ -_ 0# 1# gcd
      division : ∀ n m {m≉0 : m ≉ 0#} → n ≈ ((m * (n div m) {m≉0}) + (n mod m) {m≉0})
      modulus : ∀ n m {m≉0 : m ≉ 0#} → Remainder n m {m≉0}
      div-cong : ∀ {x₁ x₂} {y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → ∀ {y₁≉0 y₂≉0} → (x₁ div y₁) {y₁≉0} ≈ (x₂ div y₂) {y₂≉0}
      mod-cong : ∀ {x₁ x₂} {y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → ∀ {y₁≉0 y₂≉0} → (x₁ mod y₁) {y₁≉0} ≈ (x₂ mod y₂) {y₂≉0}

    open IsUniqueFactorizationDomain isUniqueFactorizationDomain public

record IsField (_+_ _*_ : Op₂ C) (-_ : Op₁ C) (0# 1# : C) (_/_ : ∀ (n m : C) {m≉0 : m ≉ 0#} → C) (gcd : Op₂ C) : Set (c ⊔ ℓ) where
  field
    isEuclideanDomain : IsEuclideanDomain _+_ _*_ -_ 0# 1# (λ _ → 0) _/_ (λ _ _ → 0#) gcd

  open IsEuclideanDomain isEuclideanDomain public renaming (div-cong to /-cong)
  open import Relation.Binary.Reasoning.Setoid setoid

  m*[n/m]≈n : ∀ n m {m≉0 : m ≉ 0#} → (m * (n / m) {m≉0}) ≈ n
  m*[n/m]≈n n m {m≉0} = begin
    (m * (n / m) {m≉0}) ≈⟨ sym (+-identityʳ (m * (n / m) {m≉0})) ⟩
    ((m * (n / m) {m≉0}) + 0#) ≈⟨ sym (division n m) ⟩
    n ∎

  [n/m]*m≈n : ∀ n m {m≉0 : m ≉ 0#} → ((n / m) {m≉0} * m) ≈ n
  [n/m]*m≈n n m {m≉0} = begin
    ((n / m) * m) ≈⟨ *-comm (n / m) m ⟩
    (m * (n / m)) ≈⟨ m*[n/m]≈n n m ⟩
    n ∎

  /≉0 : ∀ {c₁ c₂} → c₁ ≉ 0# → (c₂≉0 : c₂ ≉ 0#) → (c₁ / c₂) {c₂≉0} ≉ 0#
  /≉0 {c₁} {c₂} c₁≉0 c₂≉0 c₁/c₂≈0 = 0#≉1# $ *-cancelˡ c₂ c₂≉0 $ begin
    c₂ * 0#                      ≈⟨ *-congˡ (sym (zeroˡ ((c₂ / c₁) {c₁≉0}))) ⟩
    c₂ * (0# * (c₂ / c₁))        ≈⟨ *-congˡ (*-congʳ (sym (c₁/c₂≈0))) ⟩
    c₂ * ((c₁ / c₂) * (c₂ / c₁)) ≈⟨ sym (*-assoc c₂  (c₁ / c₂) (c₂ / c₁)) ⟩
    (c₂ * (c₁ / c₂)) * (c₂ / c₁) ≈⟨ *-congʳ (m*[n/m]≈n c₁ c₂) ⟩
    c₁ * (c₂ / c₁)               ≈⟨ m*[n/m]≈n c₂ c₁ ⟩
    c₂                           ≈⟨ sym (*-identityʳ c₂) ⟩
    c₂ * 1#                      ∎

  infixl 7 _/-nonzero_
  _/-nonzero_ : C/0 → C/0 → C/0
  (c₁ , c₁≉0) /-nonzero (c₂ , c₂≉0) = (c₁ / c₂) {c₂≉0} , /≉0 c₁≉0 c₂≉0

  infix 8 _⁻¹
  _⁻¹ : ∀ x {x≉0 : x ≉ 0#} → C
  _⁻¹ x {x≉0} = (1# / x) {x≉0}

  ⁻¹-inverseʳ : ∀ x {x≉0 : x ≉ 0#} → (x * (x ⁻¹) {x≉0}) ≈ 1#
  ⁻¹-inverseʳ = m*[n/m]≈n 1#

  ⁻¹-inverseˡ : ∀ x {x≉0 : x ≉ 0#} → ((x ⁻¹) {x≉0} * x) ≈ 1#
  ⁻¹-inverseˡ = [n/m]*m≈n 1#

  x⁻¹≉0 : ∀ x {x≉0 : x ≉ 0#} → (x ⁻¹) {x≉0} ≉ 0#
  x⁻¹≉0 x {x≉0} = /≉0 1#≉0# x≉0
  -- 0#≉1# $ begin
  --   0# ≈⟨ sym (zeroʳ x) ⟩
  --   x * 0# ≈⟨ *-congˡ (sym x⁻¹≈0) ⟩
  --   x * (x ⁻¹) {x≉0} ≈⟨ ⁻¹-inverseʳ x ⟩
  --   1# ∎

  ⁻¹-cong : ∀ {x y} {x≉0 : x ≉ 0#} {y≉0 : y ≉ 0#} → x ≈ y → (x ⁻¹) {x≉0} ≈ (y ⁻¹) {y≉0}
  ⁻¹-cong {x} {y} {x≉0} {y≉0} x≈y = *-cancelˡ x x≉0 $ begin
    (x * (x ⁻¹)) ≈⟨ ⁻¹-inverseʳ x ⟩
    1#           ≈⟨ sym (⁻¹-inverseʳ y {y≉0}) ⟩
    (y * (y ⁻¹)) ≈⟨ *-congʳ (sym x≈y) ⟩
    (x * (y ⁻¹)) ∎

record IsDecField
  (_≈?_ : Decidable _≈_) (_+_ _*_ : Op₂ C) (-_ : Op₁ C) (0# 1# : C)
  (_/_  : ∀ (n m : C) {m≉0 : m ≉ 0#} → C) (gcd : Op₂ C) : Set (c ⊔ ℓ) where
  field
    isField : IsField _+_ _*_ -_ 0# 1# _/_ gcd

  open IsField isField public

  isDecEquivalence : IsDecEquivalence _≈_
  isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_ = _≈?_
    }

record IsFiniteField
  (_≈?_ : Decidable _≈_) (_+_ _*_ : Op₂ C) (-_ : Op₁ C) (0# 1# : C)
  (_/_  : ∀ (n m : C) {m≉0 : m ≉ 0#} → C) (gcd : Op₂ C)
  (cardinality : ℕ) : Set (suc c ⊔ ℓ) where
  field
    isDecField : IsDecField _≈?_ _+_ _*_ -_ 0# 1# _/_ gcd
    C↦Fin[cardinality] : C ⤖ Fin cardinality

  open IsDecField isDecField public
