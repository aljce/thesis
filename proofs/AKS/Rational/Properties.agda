open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong₂; isEquivalence; setoid)
open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)


open import Data.Unit using (⊤; tt)
open import Agda.Builtin.FromNat using (Number)

open import Data.Product using (_,_)

module AKS.Rational.Properties where

open import AKS.Rational.Base using (ℚ; _+_; _*_; -_; _/_; _≟_)

open import Algebra.Structures {A = ℚ} _≡_ using
  ( IsCommutativeRing; IsRing; IsAbelianGroup
  ; IsGroup; IsMonoid; IsSemigroup; IsMagma
  )
open import Algebra.Definitions {A = ℚ} _≡_ using
  ( _DistributesOver_; _DistributesOverʳ_; _DistributesOverˡ_
  ; RightIdentity; LeftIdentity; Identity; Associative; Commutative
  ; RightInverse; LeftInverse; Inverse
  )
open import AKS.Algebra.Structures ℚ _≡_ using (IsNonZeroCommutativeRing; IsIntegralDomain; IsGCDDomain; IsDecField)
open import Algebra.Bundles using (Ring; CommutativeRing)
open import AKS.Algebra.Bundles using (IntegralDomain; DecField)

open import AKS.Unsafe using (BOTTOM; ≢-irrelevant)

+-isMagma : IsMagma _+_
+-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong = cong₂ _+_
  }

+-assoc : Associative _+_
+-assoc = BOTTOM

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc = +-assoc
  }

+-comm : Commutative _+_
+-comm = BOTTOM

+-identityˡ : LeftIdentity 0 _+_
+-identityˡ = BOTTOM

open import Algebra.FunctionProperties.Consequences.Propositional using (comm+idˡ⇒idʳ; comm+invˡ⇒invʳ; comm+distrˡ⇒distrʳ)

+-identityʳ : RightIdentity 0 _+_
+-identityʳ = BOTTOM -- comm+idˡ⇒idʳ +-comm +-identityˡ

+-identity : Identity 0 _+_
+-identity = +-identityˡ , +-identityʳ

+-isMonoid : IsMonoid _+_ 0
+-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity = +-identity
  }

-‿inverseˡ : LeftInverse 0 -_ _+_
-‿inverseˡ = BOTTOM

-‿inverseʳ : RightInverse 0 -_ _+_
-‿inverseʳ = BOTTOM -- comm+invˡ⇒invʳ +-comm -‿inverseˡ

-‿inverse : Inverse 0 -_ _+_
-‿inverse = -‿inverseˡ , -‿inverseʳ

+-isGroup : IsGroup _+_ 0 -_
+-isGroup = record
  { isMonoid = +-isMonoid
  ; inverse = -‿inverse
  ; ⁻¹-cong = cong -_
  }

+-isAbelianGroup : IsAbelianGroup _+_ 0 -_
+-isAbelianGroup = record
  { isGroup = +-isGroup
  ; comm = +-comm
  }

*-isMagma : IsMagma _*_
*-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong = cong₂ _*_
  }

*-assoc : Associative _*_
*-assoc = BOTTOM

*-isSemigroup : IsSemigroup _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc = *-assoc
  }

*-comm : Commutative _*_
*-comm x y = BOTTOM

*-identityˡ : LeftIdentity 1 _*_
*-identityˡ x = BOTTOM

*-identityʳ : RightIdentity 1 _*_
*-identityʳ = BOTTOM -- comm+idˡ⇒idʳ *-comm *-identityˡ

*-identity : Identity 1 _*_
*-identity = *-identityˡ , *-identityʳ

*-isMonoid : IsMonoid _*_ 1
*-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity = *-identity
  }

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ = BOTTOM

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ = BOTTOM -- comm+distrˡ⇒distrʳ *-comm *-distribˡ-+

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

+-*-isRing : IsRing _+_ _*_ -_ 0 1
+-*-isRing = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; *-isMonoid = *-isMonoid
  ; distrib = *-distrib-+
  }

+-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0 1
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

+-*-isNonZeroCommutativeRing : IsNonZeroCommutativeRing _+_ _*_ -_ 0 1
+-*-isNonZeroCommutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  ; 0#≉1# = λ ()
  }

*-cancelˡ : ∀ x {y z} → x ≢ 0 → x * y ≡ x * z → y ≡ z
*-cancelˡ = BOTTOM

+-*-isIntegralDomain : IsIntegralDomain _+_ _*_ -_ 0 1
+-*-isIntegralDomain = record
  { isNonZeroCommutativeRing = +-*-isNonZeroCommutativeRing
  ; *-cancelˡ = *-cancelˡ
  }

+-*-integralDomain : IntegralDomain 0ℓ 0ℓ
+-*-integralDomain = record { isIntegralDomain = +-*-isIntegralDomain }

/-inverse : ∀ x y {y≢0} → x ≡ y * (x / y) {y≢0}
/-inverse x y {y≢0} = BOTTOM

open import AKS.Algebra.Consequences +-*-integralDomain using (module Inverse⇒Field)

open Inverse⇒Field _≟_ ≡-irrelevant ≢-irrelevant _/_ /-inverse
  using (gcd)
  renaming (isField to +-*-/-isField; [field] to +-*-/-field) public

+-*-/-isDecField : IsDecField _≟_ _+_ _*_ -_ 0 1 _/_ gcd
+-*-/-isDecField = record { isField = +-*-/-isField }

+-*-/-decField : DecField 0ℓ 0ℓ
+-*-/-decField = record { isDecField = +-*-/-isDecField }
