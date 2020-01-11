open import Level using (_⊔_; suc)

open import Data.Empty using (⊥)

open import Relation.Binary using (Rel; Decidable; DecSetoid)

module AKS.Algebra.Bundles where

open import AKS.Nat using (ℕ)

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Bundles using (CommutativeRing) public
open import AKS.Algebra.Structures using
  ( IsNonZeroCommutativeRing; IsIntegralDomain; IsGCDDomain
  ; IsUniqueFactorizationDomain; IsEuclideanDomain; IsField
  ; IsDecField; IsFiniteField
  ) public

record NonZeroCommutativeRing a ℓ : Set (suc (a ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set a
    _≈_     : Rel Carrier ℓ

  infix 4 _≉_
  _≉_ : Rel Carrier ℓ
  x ≉ y = x ≈ y → ⊥

  field
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
    isNonZeroCommutativeRing : IsNonZeroCommutativeRing Carrier _≈_ _+_ _*_ -_ 0# 1#

  open IsNonZeroCommutativeRing isNonZeroCommutativeRing using (isCommutativeRing; 0#≉1#; 1#≉0#; 0#≉-1#; -1#≉0#; C/0) public


  commutativeRing : CommutativeRing a ℓ
  commutativeRing = record { isCommutativeRing = isCommutativeRing }

  open CommutativeRing commutativeRing using
    ( +-rawMagma; +-magma; +-semigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; +-group; +-abelianGroup; _-_
    ; *-rawMonoid; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne; commutativeSemiring
    ; ring; setoid; isEquivalence
    ) public

record IntegralDomain a ℓ : Set (suc (a ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set a
    _≈_     : Rel Carrier ℓ

  infix 4 _≉_
  _≉_ : Rel Carrier ℓ
  x ≉ y = x ≈ y → ⊥

  field
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
    isIntegralDomain : IsIntegralDomain Carrier _≈_ _+_ _*_ -_ 0# 1#

  open IsIntegralDomain isIntegralDomain using (isNonZeroCommutativeRing; *-cancelˡ; *-cancelʳ; *≉0; _*/0_) public

  nonZeroCommutativeRing : NonZeroCommutativeRing a ℓ
  nonZeroCommutativeRing = record { isNonZeroCommutativeRing = isNonZeroCommutativeRing }

  open NonZeroCommutativeRing nonZeroCommutativeRing using
    ( +-rawMagma; +-magma; +-semigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; +-group; +-abelianGroup; _-_
    ; *-rawMonoid; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne; commutativeSemiring
    ; ring; commutativeRing
    ; 0#≉1#; 1#≉0#; 0#≉-1#; -1#≉0#; C/0
    ; setoid; isEquivalence
    ) public


record GCDDomain a ℓ : Set (suc (a ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set a
    _≈_     : Rel Carrier ℓ

  infix 4 _≉_
  _≉_ : Rel Carrier ℓ
  x ≉ y = x ≈ y → ⊥

  field
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
    gcd     : Op₂ Carrier
    isGCDDomain : IsGCDDomain Carrier _≈_ _+_ _*_ -_ 0# 1# gcd

  open IsGCDDomain isGCDDomain using (isIntegralDomain) public

  integralDomain : IntegralDomain a ℓ
  integralDomain = record { isIntegralDomain = isIntegralDomain }

  open IntegralDomain integralDomain using
    ( +-rawMagma; +-magma; +-semigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; +-group; +-abelianGroup; _-_
    ; *-rawMonoid; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne; commutativeSemiring
    ; ring; commutativeRing; nonZeroCommutativeRing
    ; 0#≉1#; 1#≉0#; 0#≉-1#; -1#≉0#
    ; C/0; *-cancelˡ; *-cancelʳ; *≉0; _*/0_
    ; setoid; isEquivalence
    ) public

record UniqueFactorizationDomain a ℓ : Set (suc (a ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set a
    _≈_     : Rel Carrier ℓ

  infix 4 _≉_
  _≉_ : Rel Carrier ℓ
  x ≉ y = x ≈ y → ⊥

  field
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
    gcd     : Op₂ Carrier
    isUniqueFactorizationDomain : IsUniqueFactorizationDomain Carrier _≈_ _+_ _*_ -_ 0# 1# gcd

  open IsUniqueFactorizationDomain isUniqueFactorizationDomain using (isGCDDomain) public

  gcdDomain : GCDDomain a ℓ
  gcdDomain = record { isGCDDomain = isGCDDomain }

  open GCDDomain gcdDomain using
    ( +-rawMagma; +-magma; +-semigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; +-group; +-abelianGroup; _-_
    ; *-rawMonoid; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne; commutativeSemiring
    ; ring; commutativeRing; nonZeroCommutativeRing
    ; 0#≉1#; 1#≉0#; 0#≉-1#; -1#≉0#
    ; C/0; *-cancelˡ; *-cancelʳ; *≉0; _*/0_
    ; setoid; isEquivalence
    ) public

record EuclideanDomain a ℓ : Set (suc (a ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 7 _div_
  infixl 7 _mod_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set a
    _≈_     : Rel Carrier ℓ

  infix 4 _≉_
  _≉_ : Rel Carrier ℓ
  x ≉ y = x ≈ y → ⊥

  field
    _+_   : Op₂ Carrier
    _*_   : Op₂ Carrier
    -_    : Op₁ Carrier
    0#    : Carrier
    1#    : Carrier
    ∣_∣   : ∀ n {n≉0 : n ≉ 0#} → ℕ
    _div_ : ∀ (n m : Carrier) {m≉0 : m ≉ 0#} → Carrier
    _mod_ : ∀ (n m : Carrier) {m≉0 : m ≉ 0#} → Carrier
    gcd   : Op₂ Carrier
    isEuclideanDomain : IsEuclideanDomain Carrier _≈_ _+_ _*_ -_ 0# 1# ∣_∣ _div_ _mod_ gcd

  open import AKS.Algebra.Structures Carrier _≈_ using (module Modulus)
  open Modulus 0# ∣_∣ _mod_ using (Remainder; 0≈; 0≉)
  open IsEuclideanDomain isEuclideanDomain using
    ( isUniqueFactorizationDomain
    ; division; modulus
    ) public

  uniqueFactorizationDomain : UniqueFactorizationDomain a ℓ
  uniqueFactorizationDomain = record { isUniqueFactorizationDomain = isUniqueFactorizationDomain }

  open UniqueFactorizationDomain uniqueFactorizationDomain using
    ( +-rawMagma; +-magma; +-semigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; +-group; +-abelianGroup; _-_
    ; *-rawMonoid; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne; commutativeSemiring
    ; ring; commutativeRing; nonZeroCommutativeRing
    ; 0#≉1#; 1#≉0#; 0#≉-1#; -1#≉0#
    ; C/0; *-cancelˡ; *-cancelʳ; *≉0; _*/0_
    ; setoid; isEquivalence
    ) public

record Field a ℓ : Set (suc (a ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 7 _/_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set a
    _≈_     : Rel Carrier ℓ

  infix 4 _≉_
  _≉_ : Rel Carrier ℓ
  x ≉ y = x ≈ y → ⊥

  field
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
    _/_     : ∀ (n m : Carrier) {m≉0 : m ≉ 0#} → Carrier
    gcd     : Op₂ Carrier
    isField : IsField Carrier _≈_ _+_ _*_ -_ 0# 1# _/_ gcd

  open IsField isField using
    ( isEuclideanDomain
    ; m*[n/m]≈n; [n/m]*m≈n; /-cong
    ; _⁻¹; ⁻¹-inverseʳ; ⁻¹-inverseˡ
    ; x⁻¹≉0; ⁻¹-cong
    )public

  euclideanDomain : EuclideanDomain a ℓ
  euclideanDomain = record { isEuclideanDomain = isEuclideanDomain }

  open EuclideanDomain euclideanDomain using
    ( +-rawMagma; +-magma; +-semigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; +-group; +-abelianGroup; _-_
    ; *-rawMonoid; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne; commutativeSemiring
    ; ring; commutativeRing; nonZeroCommutativeRing
    ; 0#≉1#; 1#≉0#; 0#≉-1#; -1#≉0#
    ; C/0; *-cancelˡ; *-cancelʳ; *≉0; _*/0_
    ; setoid; isEquivalence
    ) public

record DecField a ℓ : Set (suc (a ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 7 _/_
  infixl 6 _+_
  infix  4 _≈_
  infix  4 _≈?_
  field
    Carrier : Set a
    _≈_     : Rel Carrier ℓ
    _≈?_    : Decidable _≈_

  infix 4 _≉_
  _≉_ : Rel Carrier ℓ
  x ≉ y = x ≈ y → ⊥

  field
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
    _/_     : ∀ (n m : Carrier) {m≉0 : m ≉ 0#} → Carrier
    gcd     : Op₂ Carrier
    isDecField : IsDecField Carrier _≈_ _≈?_ _+_ _*_ -_ 0# 1# _/_ gcd

  open IsDecField isDecField using (isField; isDecEquivalence) public

  [field] : Field a ℓ
  [field] = record { isField = isField }

  decSetoid : DecSetoid a ℓ
  decSetoid = record { isDecEquivalence = isDecEquivalence }

  open Field [field] using
    ( +-rawMagma; +-magma; +-semigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; +-group; +-abelianGroup; _-_
    ; *-rawMonoid; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne; commutativeSemiring
    ; ring; commutativeRing; nonZeroCommutativeRing
    ; 0#≉1#; 1#≉0#; 0#≉-1#; -1#≉0#
    ; C/0; *-cancelˡ; *-cancelʳ; *≉0; _*/0_
    ; m*[n/m]≈n; [n/m]*m≈n; /-cong
    ; _⁻¹; ⁻¹-inverseʳ; ⁻¹-inverseˡ
    ; x⁻¹≉0; ⁻¹-cong
    ; setoid; isEquivalence
    ) public

record FiniteField a ℓ : Set (suc (a ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 7 _/_
  infixl 6 _+_
  infix  4 _≈_
  infix  4 _≈?_
  field
    Carrier : Set a
    _≈_     : Rel Carrier ℓ
    _≈?_    : Decidable _≈_

  infix 4 _≉_
  _≉_ : Rel Carrier ℓ
  x ≉ y = x ≈ y → ⊥

  field
    _+_  : Op₂ Carrier
    _*_  : Op₂ Carrier
    -_   : Op₁ Carrier
    0#   : Carrier
    1#   : Carrier
    _/_  : ∀ (n m : Carrier) {m≉0 : m ≉ 0#} → Carrier
    gcd  : Op₂ Carrier
    cardinality   : ℕ
    isFiniteField : IsFiniteField Carrier _≈_ _≈?_ _+_ _*_ -_ 0# 1# _/_ gcd cardinality

  open IsFiniteField isFiniteField using (isDecField) public

  decField : DecField a ℓ
  decField = record { isDecField = isDecField }

  open DecField decField using
    ( +-rawMagma; +-magma; +-semigroup
    ; *-rawMagma; *-magma; *-semigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; +-group; +-abelianGroup; _-_
    ; *-rawMonoid; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne; commutativeSemiring
    ; ring; commutativeRing; nonZeroCommutativeRing
    ; 0#≉1#; 1#≉0#; 0#≉-1#; -1#≉0#
    ; C/0; *-cancelˡ; *-cancelʳ; *≉0; _*/0_
    ; m*[n/m]≈n; [n/m]*m≈n; /-cong
    ; _⁻¹; ⁻¹-inverseʳ; ⁻¹-inverseˡ
    ; x⁻¹≉0; ⁻¹-cong
    ; setoid; isEquivalence; decSetoid; isDecEquivalence
    ) public
