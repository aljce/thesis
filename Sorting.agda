open import Function using (const)

open import Level using (_⊔_)

open import Relation.Binary using (Rel; IsTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; _+_)
open import Data.Maybe using (Maybe)
open Maybe
open import Data.Vec using (Vec)
open Vec

module Sorting {a r} {A : Set a} (_≤_ : Rel A r) (≤-isTotalOrder : IsTotalOrder _≡_ _≤_) where

open import Heap.Indexed _≤_ ≤-isTotalOrder (const ⊤)

data Vecᵇ (bot : Bound) (top : Bound) : ℕ → Set (a ⊔ r) where
  Nil : bot ≤ᵇ top → Vecᵇ bot top 0
  _∧_∷_ : ∀ {n} x → bot ≤ᵇ ⟨ x ⟩ → Vecᵇ ⟨ x ⟩ top n → Vecᵇ bot top (1 + n)

heapify : ∀ {n} → Vec A (1 + n) → Heap -∞ (1 + n)
heapify (a ∷ []) = singleton a (-∞≤ ⟨ a ⟩) tt
heapify (a ∷ b ∷ bs) = insert a (-∞≤ ⟨ a ⟩) tt (heapify (b ∷ bs))

elems : ∀ {n} {bot} → Heap bot (1 + n) → Vecᵇ bot +∞ (1 + n)
elems heap₁ with min-view heap₁
... | Node min-key bot≤min-key tt [] = min-key ∧ bot≤min-key ∷ Nil (⟨ min-key ⟩ ≤+∞)
... | Node min-key bot≤min-key tt [ heap₂ ] = min-key ∧ bot≤min-key ∷ elems heap₂

heapsort : ∀ {n} → Vec A n → Vecᵇ -∞ +∞ n
heapsort [] = Nil (-∞≤ +∞)
heapsort (x ∷ xs) = elems (heapify (x ∷ xs))
