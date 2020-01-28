open import Function using (_$_)

open import Relation.Binary using (Setoid)

open import Data.Product using (_,_)

open import Algebra.Bundles using (RawGroup; RawRing)
open import Algebra.Structures using (IsGroup; IsAbelianGroup; IsRing; IsCommutativeRing)
open import AKS.Algebra.Structures using (IsNonZeroCommutativeRing; IsIntegralDomain)
open import AKS.Algebra.Morphism.Structures using (IsGroupHomomorphism; IsGroupMonomorphism; IsRingHomomorphism; IsRingMonomorphism)

module AKS.Algebra.Morphism.Consequences where

module GroupConsequences {c₁ c₂ ℓ₁ ℓ₂} {G₁ : RawGroup c₁ ℓ₁} {G₂ : RawGroup c₂ ℓ₂} {⟦_⟧} (isGroupMonomorphism : IsGroupMonomorphism G₁ G₂ ⟦_⟧) where
  open RawGroup G₁ using () renaming (Carrier to C₁; _∙_ to _+₁_; _⁻¹ to -₁_; ε to ε₁; _≈_ to _≈₁_; rawMonoid to +₁-rawMonoid)
  open RawGroup G₂ using () renaming (Carrier to C₂; _∙_ to _+₂_; _⁻¹ to -₂_; ε to ε₂; _≈_ to _≈₂_; rawMonoid to +₂-rawMonoid)
  open IsGroupMonomorphism isGroupMonomorphism using (injective; +-homo; -‿homo; ε-homo; +-isMonoidMonomorphism; ⟦⟧-cong)
  open import Algebra.Morphism.MonoidMonomorphism +-isMonoidMonomorphism using () renaming (isMonoid to +₂-isMonoid→+₁-isMonoid; comm to +₂-comm→+₁-comm)

  module _ (G₂-isGroup : IsGroup _≈₂_ _+₂_ ε₂ -₂_) where
    open IsGroup G₂-isGroup using (setoid) renaming (isMonoid to +₂-isMonoid; ⁻¹-cong to -‿cong₂; inverseˡ to -‿inverseˡ₂; inverseʳ to -‿inverseʳ₂; ∙-congˡ to +-congˡ; ∙-congʳ to +-congʳ)
    open Setoid setoid using (sym)
    open import Relation.Binary.Reasoning.Setoid setoid
    open import Algebra.Definitions _≈₁_ using (LeftInverse; RightInverse; Inverse; Congruent₁)

    -‿inverseˡ₁ : LeftInverse ε₁ -₁_ _+₁_
    -‿inverseˡ₁ x = injective $ begin
      ⟦ -₁ x +₁ x ⟧     ≈⟨ +-homo (-₁ x) x ⟩
      ⟦ -₁ x ⟧ +₂ ⟦ x ⟧ ≈⟨ +-congʳ (-‿homo x) ⟩
      -₂ ⟦ x ⟧ +₂ ⟦ x ⟧ ≈⟨ -‿inverseˡ₂ ⟦ x ⟧ ⟩
      ε₂                ≈⟨ sym ε-homo ⟩
      ⟦ ε₁ ⟧            ∎


    -‿inverseʳ₁ : RightInverse ε₁ -₁_ _+₁_
    -‿inverseʳ₁ x = injective $ begin
      ⟦ x +₁ -₁ x ⟧     ≈⟨ +-homo x (-₁ x) ⟩
      ⟦ x ⟧ +₂ ⟦ -₁ x ⟧ ≈⟨ +-congˡ (-‿homo x) ⟩
      ⟦ x ⟧ +₂ -₂ ⟦ x ⟧ ≈⟨ -‿inverseʳ₂ ⟦ x ⟧ ⟩
      ε₂                ≈⟨ sym ε-homo ⟩
      ⟦ ε₁ ⟧            ∎

    -‿inverse₁ : Inverse ε₁ -₁_ _+₁_
    -‿inverse₁ = -‿inverseˡ₁ , -‿inverseʳ₁

    -‿cong₁ : Congruent₁ -₁_
    -‿cong₁ {x} {y} x≈y = injective $ begin
      ⟦ -₁ x ⟧ ≈⟨ -‿homo x ⟩
      -₂ ⟦ x ⟧ ≈⟨ -‿cong₂ (⟦⟧-cong x≈y) ⟩
      -₂ ⟦ y ⟧ ≈⟨ sym (-‿homo y) ⟩
      ⟦ -₁ y ⟧ ∎

    G₂-isGroup→G₁-isGroup : IsGroup _≈₁_ _+₁_ ε₁ -₁_
    G₂-isGroup→G₁-isGroup = record
      { isMonoid = +₂-isMonoid→+₁-isMonoid +₂-isMonoid
      ; inverse = -‿inverse₁
      ; ⁻¹-cong = -‿cong₁
      }

  module _ (G₂-isAbelianGroup : IsAbelianGroup _≈₂_ _+₂_ ε₂ -₂_) where
    open IsAbelianGroup G₂-isAbelianGroup using () renaming (isGroup to G₂-isGroup; isMagma to +₂-isMagma; comm to +₂-comm)

    G₂-isAbelianGroup→G₁-isAbelianGroup : IsAbelianGroup _≈₁_ _+₁_ ε₁ -₁_
    G₂-isAbelianGroup→G₁-isAbelianGroup = record
      { isGroup = G₂-isGroup→G₁-isGroup G₂-isGroup
      ; comm = +₂-comm→+₁-comm +₂-isMagma +₂-comm
      }


module RingConsequences {c₁ c₂ ℓ₁ ℓ₂} {R₁ : RawRing c₁ ℓ₁} {R₂ : RawRing c₂ ℓ₂} {⟦_⟧} (isRingMonomorphism : IsRingMonomorphism R₁ R₂ ⟦_⟧) where
  open RawRing R₁ using () renaming (Carrier to C₁; _+_ to _+₁_; _*_ to _*₁_; -_ to -₁_; 0# to 0#₁; 1# to 1#₁; _≈_ to _≈₁_)
  open RawRing R₂ using () renaming (Carrier to C₂; _+_ to _+₂_; _*_ to _*₂_; -_ to -₂_; 0# to 0#₂; 1# to 1#₂; _≈_ to _≈₂_)
  open IsRingMonomorphism isRingMonomorphism using (injective; +-homo; *-homo; 0#-homo; 1#-homo; ⟦⟧-cong; *-isMonoidMonomorphism; +-isGroupMonomorphism)
  open import Algebra.Morphism.MonoidMonomorphism *-isMonoidMonomorphism using () renaming (isMonoid to *₂-isMonoid→*₁-isMonoid; comm to *₂-comm→*₁-comm)

  module _ (R₂-isRing : IsRing _≈₂_ _+₂_ _*₂_ -₂_ 0#₂ 1#₂) where
    open IsRing R₂-isRing using (setoid; +-cong; *-congˡ; *-congʳ) renaming (distribʳ to distribʳ₁; distribˡ to distribˡ₁; *-isMonoid to *₂-isMonoid; +-isAbelianGroup to +₂-isAbelianGroup)
    open Setoid setoid using (sym)
    open import Relation.Binary.Reasoning.Setoid setoid
    open import Algebra.Definitions _≈₁_ using (_DistributesOverʳ_; _DistributesOverˡ_; _DistributesOver_)

    distribʳ : _*₁_ DistributesOverʳ _+₁_
    distribʳ r x y = injective $ begin
      ⟦ (x +₁ y) *₁ r ⟧                ≈⟨ *-homo (x +₁ y) r ⟩
      ⟦ x +₁ y ⟧ *₂ ⟦ r ⟧              ≈⟨ *-congʳ (+-homo x y) ⟩
      (⟦ x ⟧ +₂ ⟦ y ⟧) *₂ ⟦ r ⟧        ≈⟨ distribʳ₁ ⟦ r ⟧ ⟦ x ⟧ ⟦ y ⟧ ⟩
      ⟦ x ⟧ *₂ ⟦ r ⟧ +₂ ⟦ y ⟧ *₂ ⟦ r ⟧ ≈⟨ +-cong (sym (*-homo x r )) (sym (*-homo y r)) ⟩
      ⟦ x *₁ r ⟧ +₂ ⟦ y *₁ r ⟧         ≈⟨ sym (+-homo (x *₁ r) (y *₁ r)) ⟩
      ⟦ x *₁ r +₁ y *₁ r ⟧ ∎

    distribˡ : _*₁_ DistributesOverˡ _+₁_
    distribˡ r x y = injective $ begin
      ⟦ r *₁ (x +₁ y) ⟧                ≈⟨ *-homo r (x +₁ y) ⟩
      ⟦ r ⟧ *₂ ⟦ x +₁ y ⟧              ≈⟨ *-congˡ (+-homo x y) ⟩
      ⟦ r ⟧ *₂ (⟦ x ⟧ +₂ ⟦ y ⟧)        ≈⟨ distribˡ₁ ⟦ r ⟧ ⟦ x ⟧ ⟦ y ⟧ ⟩
      ⟦ r ⟧ *₂ ⟦ x ⟧ +₂ ⟦ r ⟧ *₂ ⟦ y ⟧ ≈⟨ +-cong (sym (*-homo r x)) (sym (*-homo r y)) ⟩
      ⟦ r *₁ x ⟧ +₂ ⟦ r *₁ y ⟧         ≈⟨ sym (+-homo (r *₁ x) (r *₁ y)) ⟩
      ⟦ r *₁ x +₁ r *₁ y ⟧ ∎

    distrib : _*₁_ DistributesOver _+₁_
    distrib = distribˡ , distribʳ

    open GroupConsequences +-isGroupMonomorphism

    R₂-isRing→R₁-isRing : IsRing _≈₁_ _+₁_ _*₁_ -₁_ 0#₁ 1#₁
    R₂-isRing→R₁-isRing = record
      { +-isAbelianGroup = G₂-isAbelianGroup→G₁-isAbelianGroup +₂-isAbelianGroup
      ; *-isMonoid = *₂-isMonoid→*₁-isMonoid *₂-isMonoid
      ; distrib = distrib
      }

  module _ (R₂-isCommutativeRing : IsCommutativeRing _≈₂_ _+₂_ _*₂_ -₂_ 0#₂ 1#₂) where
    open IsCommutativeRing R₂-isCommutativeRing using () renaming (isRing to R₂-isRing; *-comm to *₂-comm; *-isMagma to *₂-isMagma)

    R₂-isCommutativeRing→R₁-isCommutativeRing : IsCommutativeRing _≈₁_ _+₁_ _*₁_ -₁_ 0#₁ 1#₁
    R₂-isCommutativeRing→R₁-isCommutativeRing = record
      { isRing = R₂-isRing→R₁-isRing R₂-isRing
      ; *-comm = *₂-comm→*₁-comm *₂-isMagma *₂-comm
      }

  module _ (R₂-isNonZeroCommutativeRing : IsNonZeroCommutativeRing C₂ _≈₂_ _+₂_ _*₂_ -₂_ 0#₂ 1#₂) where
    open IsNonZeroCommutativeRing R₂-isNonZeroCommutativeRing using (setoid) renaming (isCommutativeRing to R₂-isCommutativeRing; 0#≉1# to 0#₂≉1#₂)
    open Setoid setoid using (sym)
    open import Relation.Binary.Reasoning.Setoid setoid
    open import AKS.Algebra.Structures C₁ _≈₁_ using () renaming (_≉_ to _≉₁_)

    0#₁≉1#₁ : 0#₁ ≉₁ 1#₁
    0#₁≉1#₁ 0#₁≈1#₁ = 0#₂≉1#₂ $ begin
      0#₂     ≈⟨ sym 0#-homo ⟩
      ⟦ 0#₁ ⟧ ≈⟨ ⟦⟧-cong 0#₁≈1#₁ ⟩
      ⟦ 1#₁ ⟧ ≈⟨ 1#-homo ⟩
      1#₂ ∎

    R₂-isNonZeroCommutativeRing→R₁-isNonZeroCommutativeRing : IsNonZeroCommutativeRing C₁ _≈₁_ _+₁_ _*₁_ -₁_ 0#₁ 1#₁
    R₂-isNonZeroCommutativeRing→R₁-isNonZeroCommutativeRing = record
      { isCommutativeRing = R₂-isCommutativeRing→R₁-isCommutativeRing R₂-isCommutativeRing
      ; 0#≉1# = 0#₁≉1#₁
      }

  module _ (R₂-isIntegralDomain : IsIntegralDomain C₂ _≈₂_ _+₂_ _*₂_ -₂_ 0#₂ 1#₂) where
    open IsIntegralDomain R₂-isIntegralDomain using (setoid) renaming (isNonZeroCommutativeRing to R₂-isNonZeroCommutativeRing; *-cancelˡ to *₂-cancelˡ)
    open Setoid setoid using (sym)
    open import Relation.Binary.Reasoning.Setoid setoid
    open import AKS.Algebra.Structures C₁ _≈₁_ using () renaming (_≉_ to _≉₁_)
    open import AKS.Algebra.Structures C₂ _≈₂_ using () renaming (_≉_ to _≉₂_)

    *-cancelˡ : ∀ x {y z} → x ≉₁ 0#₁ → x *₁ y ≈₁ x *₁ z → y ≈₁ z
    *-cancelˡ x {y} {z} x≉0 x*y≈x*z = injective $ *₂-cancelˡ ⟦ x ⟧ ⟦x⟧≉0 $ begin
      ⟦ x ⟧ *₂ ⟦ y ⟧ ≈⟨ sym (*-homo x y) ⟩
      ⟦ x *₁ y ⟧     ≈⟨ ⟦⟧-cong x*y≈x*z ⟩
      ⟦ x *₁ z ⟧     ≈⟨ *-homo x z ⟩
      ⟦ x ⟧ *₂ ⟦ z ⟧ ∎
      where
      ⟦x⟧≉0 : ⟦ x ⟧ ≉₂ 0#₂
      ⟦x⟧≉0 ⟦x⟧≈0 = x≉0 $ injective $ begin
        ⟦ x ⟧   ≈⟨ ⟦x⟧≈0 ⟩
        0#₂     ≈⟨ sym 0#-homo ⟩
        ⟦ 0#₁ ⟧ ∎


    R₂-isIntegralDomain→R₁-isIntegralDomain : IsIntegralDomain C₁ _≈₁_ _+₁_ _*₁_ -₁_ 0#₁ 1#₁
    R₂-isIntegralDomain→R₁-isIntegralDomain = record
      { isNonZeroCommutativeRing = R₂-isNonZeroCommutativeRing→R₁-isNonZeroCommutativeRing R₂-isNonZeroCommutativeRing
      ; *-cancelˡ = *-cancelˡ
      }
