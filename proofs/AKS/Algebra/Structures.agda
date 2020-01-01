open import Level using (_⊔_; suc)
open import Function using (_$_; _⤖_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

open import Data.Empty using (⊥)
open import Data.Product using (∃-syntax)
open import Data.Sum using (_⊎_)

-- open import Function.Bijection using (_⤖_)

module AKS.Algebra.Structures {a ℓ} (A : Set a) (_≈_ : Rel A ℓ) where

open import AKS.Nat using (ℕ; _<_)
open import AKS.Fin using (Fin)

open import Algebra.FunctionProperties using (Op₂; Op₁)
open import Algebra.Structures _≈_ using (IsCommutativeRing)

_≉_ : Rel A ℓ
x ≉ y = x ≈ y → ⊥

record IsNonZeroCommutativeRing (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    0#≉1# : 0# ≉ 1#
    isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0# 1#

  open IsCommutativeRing isCommutativeRing public

record IsIntegralDomain (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    *-cancelˡ : ∀ x {y z} → x ≉ 0# → (x * y) ≈ (x * z) → y ≈ z
    isNonZeroCommutativeRing : IsNonZeroCommutativeRing _+_ _*_ -_ 0# 1#

  open IsNonZeroCommutativeRing isNonZeroCommutativeRing public

  *-cancelʳ : ∀ x {y z} → x ≉ 0# → (y * x) ≈ (z * x) → y ≈ z
  *-cancelʳ x {y} {z} x≉0 y*x≈z*x = *-cancelˡ x x≉0 $ begin
    (x * y) ≈⟨ *-comm x y ⟩
    (y * x) ≈⟨ y*x≈z*x ⟩
    (z * x) ≈⟨ *-comm z x ⟩
    (x * z) ∎
    where
    open import Relation.Binary.Reasoning.Setoid setoid

record IsGCDDomain (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isIntegralDomain : IsIntegralDomain _+_ _*_ -_ 0# 1#
    -- TODO define gcd

  open IsIntegralDomain isIntegralDomain public

record IsUniqueFactorizationDomain (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isGCDDomain : IsGCDDomain _+_ _*_ -_ 0# 1#
    -- TODO define factorization

  open IsGCDDomain isGCDDomain public

module _
  (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) (∣_∣ : ∀ n {n≉0 : n ≉ 0#} → ℕ)
  (_div_ : ∀ (n m : A) {m≉0 : m ≉ 0#} → A) (_mod_ : ∀ (n m : A) {m≉0 : m ≉ 0#} → A)
  where
  data Remainder (n : A) (m : A) {m≉0 : m ≉ 0#} : Set (a ⊔ ℓ) where
    0≈ : (r≈0 : (n mod m) {m≉0} ≈ 0#) → Remainder n m
    0≉ : (r≉0 : (n mod m) {m≉0} ≉ 0#) → ∣ n mod m ∣ {r≉0} < ∣ m ∣ {m≉0} → Remainder n m

  record IsEuclideanDomain  : Set (a ⊔ ℓ) where
    field
      division : ∀ n m {m≉0 : m ≉ 0#} → n ≈ ((m * (n div m) {m≉0}) + (n mod m) {m≉0})
      modulus : ∀ n m {m≉0 : m ≉ 0#} → Remainder n m {m≉0}
      isUniqueFactorizationDomain : IsUniqueFactorizationDomain _+_ _*_ -_ 0# 1#

    open IsUniqueFactorizationDomain isUniqueFactorizationDomain public

record IsField (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) (_/_ : ∀ (n m : A) {m≉0 : m ≉ 0#} → A) : Set (a ⊔ ℓ) where
  field
    isEuclideanDomain : IsEuclideanDomain _+_ _*_ -_ 0# 1# (λ _ → 0) _/_ (λ _ _ → 0#)

  open IsEuclideanDomain isEuclideanDomain public
  open import Relation.Binary.Reasoning.Setoid setoid

  m*[n/m]≈n : ∀ n m {m≉0 : m ≉ 0#} → (m * (n / m) {m≉0}) ≈ n
  m*[n/m]≈n n m {m≉0} = begin
    (m * (n / m) {m≉0}) ≈⟨ sym (+-identityʳ (m * (n / m) {m≉0})) ⟩
    ((m * (n / m) {m≉0}) + 0#) ≈⟨ sym (division n m) ⟩
    n ∎

  /-cong : ∀ {n₁ n₂} {m₁ m₂} {m₁≉0 : m₁ ≉ 0#} {m₂≉0 :  m₂ ≉ 0#} → n₁ ≈ n₂ → m₁ ≈ m₂ → (n₁ / m₁) {m₁≉0} ≈ (n₂ / m₂) {m₂≉0}
  /-cong {n₁} {n₂} {m₁} {m₂} {m₁≉0} {m₂≉0} n₁≈n₂ m₁≈m₂ = *-cancelˡ m₁ m₁≉0 $ begin
    (m₁ * (n₁ / m₁)) ≈⟨ m*[n/m]≈n n₁ m₁ ⟩
    n₁               ≈⟨ n₁≈n₂ ⟩
    n₂               ≈⟨ sym (m*[n/m]≈n n₂ m₂) ⟩
    (m₂ * (n₂ / m₂)) ≈⟨ *-congʳ (sym m₁≈m₂) ⟩
    (m₁ * (n₂ / m₂)) ∎

  _⁻¹ : ∀ x {x≉0 : x ≉ 0#} → A
  _⁻¹ x {x≉0} = (1# / x) {x≉0}

  ⁻¹-inverseʳ : ∀ x {x≉0 : x ≉ 0#} → (x * (x ⁻¹) {x≉0}) ≈ 1#
  ⁻¹-inverseʳ = m*[n/m]≈n 1#

  ⁻¹-inverseˡ : ∀ x {x≉0 : x ≉ 0#} → ((x ⁻¹) {x≉0} * x) ≈ 1#
  ⁻¹-inverseˡ x {x≉0} = begin
    ((x ⁻¹) {x≉0} * x) ≈⟨ *-comm (x ⁻¹) x ⟩
    (x * (x ⁻¹) {x≉0}) ≈⟨ ⁻¹-inverseʳ x ⟩
    1# ∎

  x⁻¹≉0 : ∀ x {x≉0 : x ≉ 0#} → (x ⁻¹) {x≉0} ≉ 0#
  x⁻¹≉0 x {x≉0} x⁻¹≈0 = 0#≉1# $ begin
    0# ≈⟨ sym (zeroʳ x) ⟩
    x * 0# ≈⟨ *-congˡ (sym x⁻¹≈0) ⟩
    x * (x ⁻¹) {x≉0} ≈⟨ ⁻¹-inverseʳ x ⟩
    1# ∎

  ⁻¹-cong : ∀ {x y} {x≉0 : x ≉ 0#} {y≉0 : y ≉ 0#} → x ≈ y → (x ⁻¹) {x≉0} ≈ (y ⁻¹) {y≉0}
  ⁻¹-cong {x} {y} {x≉0} {y≉0} x≈y = *-cancelˡ x x≉0 $ begin
    (x * (x ⁻¹)) ≈⟨ ⁻¹-inverseʳ x ⟩
    1#           ≈⟨ sym (⁻¹-inverseʳ y {y≉0}) ⟩
    (y * (y ⁻¹)) ≈⟨ *-congʳ (sym x≈y) ⟩
    (x * (y ⁻¹)) ∎

record IsDecField (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) (_/_ : ∀ (n m : A) {m≉0 : m ≉ 0#} → A) : Set (a ⊔ ℓ) where
  field
    isField : IsField _+_ _*_ -_ 0# 1# _/_

  open IsField isField public

record IsFiniteField (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) (_/_ : ∀ (n m : A) {m≉0 : m ≉ 0#} → A) : Set (suc a ⊔ ℓ) where
  field
    cardinality : ℕ
    A↦Fin[cardinality] : A ⤖ Fin cardinality
    isField : IsField _+_ _*_ -_ 0# 1# _/_

  open IsField isField public
