open import Level using (_⊔_)

open import Relation.Nullary using (Dec)
open Dec
open import Relation.Binary using (Rel; IsTotalOrder; Reflexive; Transitive; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Heap.Key
  {k r} {Key : Set k}
  (_≤_ : Rel Key r) (≤-isTotalOrder : IsTotalOrder _≡_ _≤_) where

open IsTotalOrder ≤-isTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)

data Bound : Set k where
  -∞ : Bound
  ⟨_⟩ : Key → Bound
  +∞ : Bound

data _≤ᵇ_ : Rel Bound (k ⊔ r) where
  -∞≤_  : ∀ top → -∞ ≤ᵇ top
  ⟨_⟩   : ∀ {bot top} → bot ≤ top → ⟨ bot ⟩ ≤ᵇ ⟨ top ⟩
  _≤+∞  : ∀ bot → bot ≤ᵇ +∞

≤ᵇ-refl : Reflexive _≤ᵇ_
≤ᵇ-refl { -∞} = -∞≤ -∞
≤ᵇ-refl {⟨ _ ⟩} = ⟨ ≤-refl ⟩
≤ᵇ-refl {+∞} = +∞ ≤+∞

≤ᵇ-trans : Transitive _≤ᵇ_
≤ᵇ-trans {x} {y} {z} (-∞≤ _) _ = -∞≤ z
≤ᵇ-trans {x} {y} {z} ⟨ x≤y ⟩ ⟨ y≤z ⟩ = ⟨ ≤-trans x≤y y≤z ⟩
≤ᵇ-trans {x} {y} {z} _ (_ ≤+∞) = x ≤+∞
