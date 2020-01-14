open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.FromNat using (Number)

module AKS.Test where

open import AKS.Nat using ()
open import AKS.Rational using (show-ℚ)
open import AKS.Rational.Properties using (+-*-/-decField)
open import AKS.Polynomial.Base +-*-/-decField
open import AKS.Polynomial.Properties +-*-/-decField

ex : Polynomial
ex = 1ᵖ +ᵖ 𝑋^ 1 +ᵖ 𝑋^ 2

ex-unit₁ : show-Polynomial show-ℚ ex ≡ "1 + 1 * X^1 + 1 * X^2"
ex-unit₁ = refl

ex-unit₂ : show-Polynomial show-ℚ (ex *ᵖ ex) ≡ "1 + 2 * X^1 + 3 * X^2 + 2 * X^3 + 1 * X^4"
ex-unit₂ = refl

open import AKS.Unsafe using (TODO)
open import Data.Product using (_,_)

test = show-Polynomial show-ℚ ((ex divᵖ (𝑋^ 1)) {TODO})
