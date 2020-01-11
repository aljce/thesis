module AKS.Test where

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.FromNat using (Number)

open import AKS.Nat using ()
open import AKS.Rational using (show-ℚ)
open import AKS.Rational.Properties using (+-*-/-decField)
open import AKS.Polynomial.Base +-*-/-decField

ex : Polynomial
ex = 1ᵖ +ᵖ 𝑋^ 1 +ᵖ 𝑋^ 2

test = show-Polynomial show-ℚ (ex +ᵖ -ᵖ (ex *ᵖ ex))
