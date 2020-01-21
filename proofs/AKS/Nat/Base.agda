open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (False; map)
open import Function.Equivalence as FE using ()

module AKS.Nat.Base where

open import Agda.Builtin.FromNat using (Number)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≟_; _<ᵇ_; pred) public
open ℕ public
open import Data.Nat.Literals using (number)

instance
  ℕ-number : Number ℕ
  ℕ-number = number

data ℕ⁺ : Set where
  ℕ+ : ℕ → ℕ⁺

_+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
ℕ+ n +⁺ ℕ+ m = ℕ+ (suc (n + m))

_*⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
ℕ+ n *⁺ ℕ+ m = ℕ+ (n + m * (suc n))

_≟⁺_ : Decidable {A = ℕ⁺} _≡_
ℕ+ n ≟⁺ ℕ+ m = map (FE.equivalence (λ { refl → refl }) (λ { refl → refl })) (n ≟ m)

⟅_⇑⟆ : ∀ n {≢0 : False (n ≟ zero)} → ℕ⁺
⟅ suc n ⇑⟆ = ℕ+ n

⟅_⇓⟆ : ℕ⁺ → ℕ
⟅ ℕ+ n ⇓⟆ = suc n

instance
  ℕ⁺-number : Number ℕ⁺
  ℕ⁺-number = record
    { Constraint = λ n → False (n ≟ zero)
    ; fromNat = λ n {{≢0}} → ⟅ n ⇑⟆ {≢0}
    }

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

