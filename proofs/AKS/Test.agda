open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.FromNat using (Number)

module AKS.Test where

open import AKS.Nat using ()
open import AKS.Rational using (show-ℚ)
open import AKS.Rational.Properties using (+-*-/-decField)
open import AKS.Polynomial.Base +-*-/-decField
-- open import AKS.Polynomial.Properties +-*-/-decField

ex : Polynomial
ex = 1ᵖ +ᵖ 𝑋^ 1 +ᵖ 𝑋^ 2

ex-unit₁ : show-Polynomial show-ℚ ex ≡ "1 + 1 * X^1 + 1 * X^2"
ex-unit₁ = refl

ex-unit₂ : show-Polynomial show-ℚ (ex *ᵖ ex) ≡ "1 + 2 * X^1 + 3 * X^2 + 2 * X^3 + 1 * X^4"
ex-unit₂ = refl

ex₂ : Polynomial
ex₂ = 1ᵖ +ᵖ 𝑋^ 4

open import AKS.Modular.Quotient using (ℤ/[_]; _+_; _*_; _/_; _⁻¹)
open import AKS.Primality using (Prime; Prime✓)
open import AKS.Unsafe using (TODO)

11-prime : Prime
11-prime = Prime✓ 11 TODO

test : ℤ/[ 11-prime ]
test = 3 * (3 ⁻¹) {TODO}
