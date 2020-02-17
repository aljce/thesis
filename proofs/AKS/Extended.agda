open import Level using () renaming (_⊔_ to _⊔ˡ_)
open import Relation.Binary using (_⇒_; TotalOrder; Reflexive; Symmetric; Transitive; IsEquivalence; IsPreorder; Antisymmetric)

module AKS.Extended {c ℓ₁ ℓ₂} (≤-totalOrder : TotalOrder c ℓ₁ ℓ₂) where

open TotalOrder ≤-totalOrder
  using (_≈_; _≤_; total; isEquivalence)
  renaming (Carrier to C; refl to ≤-refl; reflexive to ≤-reflexive; trans to ≤-trans )
open IsEquivalence isEquivalence
  using ()
  renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

data Extended : Set c where
  -∞  : Extended
  ⟨_⟩ : C → Extended

infixl 4 _≈ᵉ_
data _≈ᵉ_ : Extended → Extended → Set (c ⊔ˡ ℓ₁) where
  -∞≈ : -∞ ≈ᵉ -∞
  ⟨_⟩ : ∀ {b t} → b ≈ t → ⟨ b ⟩ ≈ᵉ ⟨ t ⟩

≈ᵉ-refl : Reflexive _≈ᵉ_
≈ᵉ-refl { -∞} = -∞≈
≈ᵉ-refl {⟨ _ ⟩} = ⟨ ≈-refl ⟩

≈ᵉ-sym : Symmetric _≈ᵉ_
≈ᵉ-sym -∞≈ = -∞≈
≈ᵉ-sym ⟨ x≈y ⟩ = ⟨ ≈-sym x≈y ⟩

≈ᵉ-trans : Transitive _≈ᵉ_
≈ᵉ-trans -∞≈ -∞≈ = -∞≈
≈ᵉ-trans ⟨ x≈y ⟩ ⟨ y≈z ⟩ = ⟨ ≈-trans x≈y y≈z ⟩

≈ᵉ-isEquivalence : IsEquivalence _≈ᵉ_
≈ᵉ-isEquivalence = record
  { refl = ≈ᵉ-refl
  ; sym = ≈ᵉ-sym
  ; trans = ≈ᵉ-trans
  }

infixl 4 _≤ᵉ_
data _≤ᵉ_ : Extended → Extended → Set (c ⊔ˡ ℓ₂) where
  -∞≤_ : ∀ t → -∞ ≤ᵉ t
  ⟨_⟩  : ∀ {b t} → b ≤ t → ⟨ b ⟩ ≤ᵉ ⟨ t ⟩

≤ᵉ-refl : Reflexive _≤ᵉ_
≤ᵉ-refl { -∞} = -∞≤ -∞
≤ᵉ-refl {⟨ _ ⟩} = ⟨ ≤-refl ⟩

≤ᵉ-reflexive : _≈ᵉ_ ⇒ _≤ᵉ_
≤ᵉ-reflexive -∞≈ = -∞≤ -∞
≤ᵉ-reflexive ⟨ x≈y ⟩ = ⟨ ≤-reflexive x≈y ⟩

≤ᵉ-trans : Transitive _≤ᵉ_
≤ᵉ-trans {x} {y} {z} (-∞≤ _) (-∞≤ t) = -∞≤ t
≤ᵉ-trans {x} {y} {z} (-∞≤ _) ⟨ _ ⟩   = -∞≤ z
≤ᵉ-trans {x} {y} {z} ⟨ x≤y ⟩ ⟨ y≤z ⟩ = ⟨ (≤-trans x≤y y≤z) ⟩

≤ᵉ-isPreorder : IsPreorder _≈ᵉ_ _≤ᵉ_
≤ᵉ-isPreorder = record { isEquivalence = ≈ᵉ-isEquivalence ; reflexive = ≤ᵉ-reflexive ; trans = ≤ᵉ-trans }

module ≤ᵉ-Reasoning where
   open import Relation.Binary.Reasoning.Base.Double ≤ᵉ-isPreorder public
