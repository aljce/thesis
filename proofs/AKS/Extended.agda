open import Level using () renaming (_⊔_ to _⊔ˡ_)
open import Relation.Binary using (TotalOrder; Reflexive; Transitive)

module AKS.Extended {c ℓ₁ ℓ₂} (≤-totalOrder : TotalOrder c ℓ₁ ℓ₂) where

open TotalOrder ≤-totalOrder
  using (_≈_; _≤_; total)
  renaming (Carrier to C; refl to ≤-refl; trans to ≤-trans)

data Extended : Set c where
  -∞  : Extended
  ⟨_⟩ : C → Extended

data _≤ᵉ_ : Extended → Extended → Set (c ⊔ˡ ℓ₂) where
  -∞≤_ : ∀ t → -∞ ≤ᵉ t
  ⟨_⟩  : ∀ {b t} → b ≤ t → ⟨ b ⟩ ≤ᵉ ⟨ t ⟩

≤ᵉ-refl : Reflexive _≤ᵉ_
≤ᵉ-refl { -∞} = -∞≤ -∞
≤ᵉ-refl {⟨ _ ⟩} = ⟨ ≤-refl ⟩

≤ᵉ-trans : Transitive _≤ᵉ_
≤ᵉ-trans {x} {y} {z} (-∞≤ _) (-∞≤ t) = -∞≤ t
≤ᵉ-trans {x} {y} {z} (-∞≤ _) ⟨ _ ⟩   = -∞≤ z
≤ᵉ-trans {x} {y} {z} ⟨ x≤y ⟩ ⟨ y≤z ⟩ = ⟨ (≤-trans x≤y y≤z) ⟩
