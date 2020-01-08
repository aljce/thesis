module AKS.Rational.Properties where

open import AKS.Rational.Base using (ℚ; _+_; _*_; -_; _⁻¹)

open import Algebra.Structures using (IsRing)
open import Algebra.Bundles using (Ring; CommutativeRing)
open import AKS.Algebra.Bundles using (IsNonZeroCommutativeRing; NonZeroCommutativeRing)

-- +-*-isRing : IsRing _≡_ _+_ _*_ -_ 0ℚ 1ℚ
-- +-*-isRing = record
--   { +-isAbelianGroup = {!!}
--   ; *-isMonoid = {!!}
--   ; distrib = {!!} }


