open import Level using () renaming (_⊔_ to _⊔ˡ_)

open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)
open import Algebra.Bundles using (RawMonoid; RawGroup; RawRing)

open import Algebra.Morphism.Structures using (IsMonoidHomomorphism; IsMonoidMonomorphism)

module AKS.Algebra.Morphism.Structures where

module GroupMorphisms {c₁ c₂ ℓ₁ ℓ₂} (G₁ : RawGroup c₁ ℓ₁) (G₂ : RawGroup c₂ ℓ₂) where
  open RawGroup G₁ using () renaming (Carrier to C₁; _∙_ to _+₁_; _⁻¹ to -₁_; ε to ε₁; _≈_ to _≈₁_; rawMonoid to +₁-rawMonoid)
  open RawGroup G₂ using () renaming (Carrier to C₂; _∙_ to _+₂_; _⁻¹ to -₂_; ε to ε₂; _≈_ to _≈₂_; rawMonoid to +₂-rawMonoid)
  open import Algebra.Morphism.Definitions C₁ C₂ _≈₂_ using (Homomorphic₂; Homomorphic₁; Homomorphic₀)
  open import Function.Definitions _≈₁_ _≈₂_ using (Injective)

  record IsGroupHomomorphism (⟦_⟧ : C₁ → C₂) : Set (c₁ ⊔ˡ ℓ₁ ⊔ˡ ℓ₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      +-homo  : Homomorphic₂ ⟦_⟧ _+₁_ _+₂_
      -‿homo  : Homomorphic₁ ⟦_⟧ -₁_ -₂_
      ε-homo  : Homomorphic₀ ⟦_⟧ ε₁ ε₂

    open IsRelHomomorphism isRelHomomorphism public renaming (cong to ⟦⟧-cong)

    +-isMonoidHomomorphism : IsMonoidHomomorphism +₁-rawMonoid +₂-rawMonoid ⟦_⟧
    +-isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
         { isRelHomomorphism = isRelHomomorphism
         ; homo = +-homo
         }
      ; ε-homo = ε-homo
      }

  record IsGroupMonomorphism (⟦_⟧ : C₁ → C₂) : Set (c₁ ⊔ˡ ℓ₁ ⊔ˡ ℓ₂) where
    field
      isGroupHomomorphism : IsGroupHomomorphism ⟦_⟧
      injective : Injective ⟦_⟧

    open IsGroupHomomorphism isGroupHomomorphism public

    +-isMonoidMonomorphism : IsMonoidMonomorphism +₁-rawMonoid +₂-rawMonoid ⟦_⟧
    +-isMonoidMonomorphism = record
      { isMonoidHomomorphism = +-isMonoidHomomorphism
      ; injective = injective
      }

open GroupMorphisms public


module RingMorphisms {c₁ c₂ ℓ₁ ℓ₂} (R₁ : RawRing c₁ ℓ₁) (R₂ : RawRing c₂ ℓ₂) where
  open RawRing R₁ using () renaming (Carrier to C₁; _+_ to _+₁_; _*_ to _*₁_; -_ to -₁_; 0# to 0#₁; 1# to 1#₁; _≈_ to _≈₁_)
  open RawRing R₂ using () renaming (Carrier to C₂; _+_ to _+₂_; _*_ to _*₂_; -_ to -₂_; 0# to 0#₂; 1# to 1#₂; _≈_ to _≈₂_)
  open import Algebra.Morphism.Definitions C₁ C₂ _≈₂_ using (Homomorphic₂; Homomorphic₁; Homomorphic₀)
  open import Function.Definitions _≈₁_ _≈₂_ using (Injective)

  +₁-rawGroup : RawGroup c₁ ℓ₁
  +₁-rawGroup = record { Carrier = C₁ ; _≈_ = _≈₁_ ; _∙_ = _+₁_ ; _⁻¹ = -₁_ ; ε = 0#₁ }

  +₂-rawGroup : RawGroup c₂ ℓ₂
  +₂-rawGroup = record { Carrier = C₂ ; _≈_ = _≈₂_ ; _∙_ = _+₂_ ; _⁻¹ = -₂_ ; ε = 0#₂ }

  *₁-rawMonoid : RawMonoid c₁ ℓ₁
  *₁-rawMonoid = record { Carrier = C₁ ; _≈_ = _≈₁_ ; _∙_ = _*₁_ ; ε = 1#₁ }

  *₂-rawMonoid : RawMonoid c₂ ℓ₂
  *₂-rawMonoid = record { Carrier = C₂ ; _≈_ = _≈₂_ ; _∙_ = _*₂_ ; ε = 1#₂ }

  record IsRingHomomorphism (⟦_⟧ : C₁ → C₂) : Set (c₁ ⊔ˡ ℓ₁ ⊔ˡ ℓ₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      +-homo  : Homomorphic₂ ⟦_⟧ _+₁_ _+₂_
      *-homo  : Homomorphic₂ ⟦_⟧ _*₁_ _*₂_
      -‿homo  : Homomorphic₁ ⟦_⟧ -₁_ -₂_
      0#-homo : Homomorphic₀ ⟦_⟧ 0#₁ 0#₂
      1#-homo : Homomorphic₀ ⟦_⟧ 1#₁ 1#₂

    open IsRelHomomorphism isRelHomomorphism public renaming (cong to ⟦⟧-cong)

    +-isGroupHomomorphism : IsGroupHomomorphism +₁-rawGroup +₂-rawGroup ⟦_⟧
    +-isGroupHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; +-homo = +-homo
      ; -‿homo = -‿homo
      ; ε-homo = 0#-homo
      }

    *-isMonoidHomomorphism : IsMonoidHomomorphism *₁-rawMonoid *₂-rawMonoid ⟦_⟧
    *-isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = isRelHomomorphism
        ; homo = *-homo
        }
      ; ε-homo = 1#-homo
      }

  record IsRingMonomorphism (⟦_⟧ : C₁ → C₂) : Set (c₁ ⊔ˡ ℓ₁ ⊔ˡ ℓ₂) where
    field
      isRingHomomorphism : IsRingHomomorphism ⟦_⟧
      injective : Injective ⟦_⟧

    open IsRingHomomorphism isRingHomomorphism public

    +-isGroupMonomorphism : IsGroupMonomorphism +₁-rawGroup +₂-rawGroup ⟦_⟧
    +-isGroupMonomorphism = record
      { isGroupHomomorphism = +-isGroupHomomorphism
      ; injective = injective
      }

    *-isMonoidMonomorphism : IsMonoidMonomorphism *₁-rawMonoid *₂-rawMonoid ⟦_⟧
    *-isMonoidMonomorphism = record
      { isMonoidHomomorphism = *-isMonoidHomomorphism
      ; injective = injective
      }

open RingMorphisms public
