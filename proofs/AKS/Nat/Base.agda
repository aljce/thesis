open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

module AKS.Nat.Base where

open import Agda.Builtin.FromNat using (Number)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≟_; _<ᵇ_) public
open ℕ public
open import Data.Nat.Literals using (number)

instance
  ℕ-number : Number ℕ
  ℕ-number = number

infix 4 _≤_
record _≤_ (n : ℕ) (m : ℕ) : Set where
  constructor lte
  field
    k : ℕ
    ≤-proof : n + k ≡ m

infix 4 _≥_
_≥_ : ℕ → ℕ → Set
n ≥ m = m ≤ n

infix 4 _<_
_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

infix 4 _≮_
_≮_ : ℕ → ℕ → Set
n ≮ m = ¬ (n < m)

infix 4 _>_
_>_ : ℕ → ℕ → Set
n > m = m < n

infix 4 _≯_
_≯_ : ℕ → ℕ → Set
n ≯ m = m ≮ n

