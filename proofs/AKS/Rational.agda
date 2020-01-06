open import Relation.Binary.PropositionalEquality using (_≡_)

module AKS.Rational where

open import Data.Rational using (ℚ; _+_; _*_; -_; 0ℚ; 1ℚ)

open import Algebra.Structures using (IsRing)
open import Algebra.Bundles using (Ring; CommutativeRing)
open import AKS.Algebra.Bundles using (IsNonZeroCommutativeRing; NonZeroCommutativeRing)

-- +-*-isRing : IsRing _≡_ _+_ _*_ -_ 0ℚ 1ℚ
-- +-*-isRing = record
--   { +-isAbelianGroup = {!!}
--   ; *-isMonoid = {!!}
--   ; distrib = {!!} }
