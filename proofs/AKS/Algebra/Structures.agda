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
    isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0# 1#
    0#≉1# : 0# ≉ 1#

  open IsCommutativeRing isCommutativeRing public

record IsIntegralDomain (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    isNonZeroCommutativeRing : IsNonZeroCommutativeRing _+_ _*_ -_ 0# 1#
    *-cancelˡ : ∀ x {y z} → x ≉ 0# → (x * y) ≈ (x * z) → y ≈ z

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

module _ (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) (∣_∣ : ∀ n {≉0 : n ≉ 0#} → ℕ) where

  record _<ᴬ_ (r : A) (m : A) {m≉0 : m ≉ 0#} : Set (a ⊔ ℓ) where
    field
      r≉0 : r ≉ 0#
      r<m : ∣ r ∣ {r≉0} < ∣ m ∣ {m≉0}

  record Division (n : A) (m : A) {m≉0 : m ≉ 0#} : Set (a ⊔ ℓ) where
    field
      q : A
      r : A
      n≈r+m*q : n ≈ (r + (q * m))
      r≈0⊎r<m : r ≈ 0# ⊎ (r <ᴬ m) {m≉0}

  record IsEuclideanDomain : Set (a ⊔ ℓ) where
    field
      isUniqueFactorizationDomain : IsUniqueFactorizationDomain _+_ _*_ -_ 0# 1#
      _div_ : ∀ n m {m≉0 : m ≉ 0#} → Division n m {m≉0}

    open IsUniqueFactorizationDomain isUniqueFactorizationDomain public

record IsField (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) (_⁻¹ : ∀ x {≉0 : x ≉ 0#} → A) : Set (a ⊔ ℓ) where
  field
    isEuclideanDomain : IsEuclideanDomain _+_ _*_ -_ 0# 1# (λ n → 1)
    ⁻¹-inverseˡ : ∀ x {x≉0 : x ≉ 0#} → ((x ⁻¹) {x≉0} * x) ≈ 1#

  open IsEuclideanDomain isEuclideanDomain public

  ⁻¹-inverseʳ : ∀ x {x≉0 : x ≉ 0#} → (x * (x ⁻¹) {x≉0}) ≈ 1#
  ⁻¹-inverseʳ x = begin
    (x * (x ⁻¹)) ≈⟨ *-comm x (x ⁻¹) ⟩
    ((x ⁻¹) * x) ≈⟨ ⁻¹-inverseˡ x ⟩
    1# ∎
    where
    open import Relation.Binary.Reasoning.Setoid setoid

  x⁻¹≉0 : ∀ x {x≉0 : x ≉ 0#} → (x ⁻¹) {x≉0} ≉ 0#
  x⁻¹≉0 x {x≉0} x⁻¹≈0 = 0#≉1# $ begin
    0# ≈⟨ sym (zeroʳ x) ⟩
    x * 0# ≈⟨ *-congˡ (sym x⁻¹≈0) ⟩
    x * (x ⁻¹) {x≉0} ≈⟨ ⁻¹-inverseʳ x ⟩
    1# ∎
    where
    open import Relation.Binary.Reasoning.Setoid setoid

  ⁻¹-cong : ∀ {x y} {x≉0 : x ≉ 0#} {y≉0 : y ≉ 0#} → x ≈ y → (x ⁻¹) {x≉0} ≈ (y ⁻¹) {y≉0}
  ⁻¹-cong {x} {y} {x≉0} {y≉0} x≈y = *-cancelˡ x x≉0 $ begin
    (x * (x ⁻¹)) ≈⟨ ⁻¹-inverseʳ x ⟩
    1#           ≈⟨ sym (⁻¹-inverseʳ y {y≉0}) ⟩
    (y * (y ⁻¹)) ≈⟨ *-congʳ (sym x≈y) ⟩
    (x * (y ⁻¹)) ∎
    where
    open import Relation.Binary.Reasoning.Setoid setoid

  A/0 : Set (a ⊔ ℓ)
  A/0 = ∃[ x ] (x ≉ 0#)

-- record Isomorphism (From : Set) (To : Set)

record IsFiniteField (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) (_⁻¹ : ∀ x {≉0 : x ≉ 0#} → A) : Set (suc a ⊔ ℓ) where
  field
    isField : IsField _+_ _*_ -_ 0# 1# _⁻¹
    cardinality : ℕ
    A↦Fin[cardinality] : A ⤖ Fin cardinality

  open IsField isField public
