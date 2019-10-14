open import Level using (_⊔_)

open import Relation.Binary using (Rel; IsTotalOrder; Reflexive; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Nat using (ℕ; suc)
open import Data.Maybe using (Maybe)
open Maybe
open import Data.Sum using (_⊎_)
open _⊎_
open import Data.Vec using (Vec)
open Vec

module Heap.Indexed {k r v} {Key : Set k}
  (_≤_ : Rel Key r) (≤-isTotalOrder : IsTotalOrder _≡_ _≤_)
  (V : Key → Set v) where

open IsTotalOrder ≤-isTotalOrder using () renaming (total to ≤-total; refl to ≤-refl; trans to ≤-trans)

data Bound : Set k where
  -∞  : Bound
  ⟨_⟩ : Key → Bound

data _≤ᵇ_ : Rel Bound (k ⊔ r) where
  instance
    -∞≤ : ∀ {top} → -∞ ≤ᵇ top
    ⟨_⟩  : ∀ {bot top} → bot ≤ top → ⟨ bot ⟩ ≤ᵇ ⟨ top ⟩

≤ᵇ-refl : Reflexive _≤ᵇ_
≤ᵇ-refl { -∞ } = -∞≤
≤ᵇ-refl {⟨ x ⟩} = ⟨ ≤-refl ⟩

≤ᵇ-trans : Transitive _≤ᵇ_
≤ᵇ-trans -∞≤ _ = -∞≤
≤ᵇ-trans ⟨ x≤y ⟩ ⟨ y≤z ⟩ = ⟨ ≤-trans x≤y y≤z ⟩

record Heap (bot : Bound) : Set (k ⊔ r ⊔ v) where
  inductive
  constructor Node
  field
    key : Key
    val : V key
    bot≤key : bot ≤ᵇ ⟨ key ⟩
    {c} : ℕ
    children : Vec (Heap ⟨ key ⟩) c

singleton : ∀ {bot} key → bot ≤ᵇ ⟨ key ⟩ → V key → Heap bot
singleton key bound val = Node key val bound []

_∪_ : ∀ {bot} → Heap bot → Heap bot → Heap bot
Node key₁ val₁ bot≤key₁ children₁ ∪ Node key₂ val₂ bot≤key₂ children₂ with ≤-total key₁ key₂
... | inj₁ key₁≤key₂ = Node key₁ val₁ bot≤key₁ (Node key₂ val₂ ⟨ key₁≤key₂ ⟩ children₂ ∷ children₁)
... | inj₂ key₁≥key₂ = Node key₂ val₂ bot≤key₂ (Node key₁ val₁ ⟨ key₁≥key₂ ⟩ children₁ ∷ children₂)

insert : ∀ {bot} key → bot ≤ᵇ ⟨ key ⟩ → V key → Heap bot → Heap bot
insert key bound val heap = singleton key bound val ∪ heap

record Min (bot : Bound) : Set (k ⊔ r ⊔ v) where
  constructor Node
  field
    min-key : Key
    min-val : V min-key
    bot≤min-key : bot ≤ᵇ ⟨ min-key ⟩
    next-heap : Maybe (Heap ⟨ min-key ⟩)

min-view : ∀ {bot} → Heap bot → Min bot
min-view (Node key val bot≤key {0} _) = Node key val bot≤key nothing
min-view (Node key val bot≤key {suc _} hs) = Node key val bot≤key (just (mergePairs hs))
  where
  mergePairs : ∀ {c} {bot} → Vec (Heap bot) (suc c) → Heap bot
  mergePairs {_} (a ∷ []) = a
  mergePairs {_} (a ∷ b ∷ []) = a ∪ b
  mergePairs {suc (suc _)} (a ∷ b ∷ cs) = (a ∪ b) ∪ mergePairs cs
