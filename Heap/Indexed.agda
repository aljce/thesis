open import Level using (_⊔_)

open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel; IsTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-assoc; +-comm; +-identityʳ)
open import Data.Maybe using (Maybe)
open Maybe
open import Data.Sum using (_⊎_)
open _⊎_
open import Data.List using (List)
open List
open import Data.List.Relation.Unary.All using (All)
open All
open import Data.Vec using (Vec)
open Vec
open import Data.Product using (∃; _,_)

module Heap.Indexed {k r v} {Key : Set k}
  (_≤_ : Rel Key r) (≤-isTotalOrder : IsTotalOrder _≡_ _≤_)
  (V : Key → Set v) where

open import Heap.Key _≤_ ≤-isTotalOrder public

open IsTotalOrder ≤-isTotalOrder using () renaming (total to ≤-total)

sum : List ℕ → ℕ
sum [] = 0
sum (x ∷ xs) = x + sum xs

data Heap (bot : Bound) : ℕ → Set (k ⊔ r ⊔ v) where
  Node : ∀ {n} key → bot ≤ᵇ ⟨ key ⟩ → V key → {ns : List ℕ} → All (Heap ⟨ key ⟩) ns → sum ns ≡ n → Heap bot (1 + n)

singleton : ∀ {bot} key → bot ≤ᵇ ⟨ key ⟩ → V key → Heap bot 1
singleton key bound val = Node key bound val [] refl

private
  lemma₁ : ∀ {a b} → 1 + (a + b) ≡ b + (1 + a)
  lemma₁ {a} {b} rewrite +-suc a b | sym (+-comm (1 + a) b) = refl
  lemma₂ : ∀ {a b} → 1 + (a + b) ≡ a + (1 + b)
  lemma₂ {a} {b} rewrite +-suc a b = refl

_∪_ : ∀ {n m} {bot} → Heap bot n → Heap bot m → Heap bot (n + m)
Node key₁ bot≤key₁ val₁ {sizes₁} children₁ refl ∪ Node key₂ bot≤key₂ val₂ {sizes₂} children₂ refl with ≤-total key₁ key₂
... | inj₁ key₁≤key₂ = Node key₁ bot≤key₁ val₁ (Node key₂ ⟨ key₁≤key₂ ⟩ val₂ children₂ refl ∷ children₁) lemma₁
... | inj₂ key₁≥key₂ = Node key₂ bot≤key₂ val₂ (Node key₁ ⟨ key₁≥key₂ ⟩ val₁ children₁ refl ∷ children₂) lemma₂

insert : ∀ {bot} {n} key → bot ≤ᵇ ⟨ key ⟩ → V key → Heap bot n → Heap bot (1 + n)
insert key bound val heap = singleton key bound val ∪ heap

data Sized {a} (f : ℕ → Set a) : ℕ → Set a where
  [] : Sized f 0
  [_]  : ∀ {n} → f (1 + n) → Sized f (1 + n)

data Min (bot : Bound) : ℕ → Set (k ⊔ r ⊔ v) where
  Node : ∀ {n} min-key → bot ≤ᵇ ⟨ min-key ⟩ → V min-key → Sized (Heap ⟨ min-key ⟩) n → Min bot (1 + n)

mergePairs : ∀ {n} {ns} {bot} → All (Heap bot) (n ∷ ns) → Heap bot (n + sum ns)
mergePairs {n₁} {[]} (h₁ ∷ []) rewrite +-identityʳ n₁ = h₁
mergePairs {n₁} {n₂ ∷ []} (h₁ ∷ h₂ ∷ []) rewrite +-identityʳ n₂ = h₁ ∪ h₂
mergePairs {n₁} {n₂ ∷ n₃ ∷ ns} (h₁ ∷ h₂ ∷ hs) rewrite sym (+-assoc n₁ n₂ (n₃ + sum ns)) = (h₁ ∪ h₂) ∪ mergePairs hs

min-view : ∀ {n} {bot} → Heap bot n → Min bot n
min-view {bot} (Node min-key bot≤min-key min-val [] refl) = Node min-key bot≤min-key min-val []
min-view {bot} (Node min-key bot≤min-key min-val {suc _ ∷ _} hs refl) with mergePairs hs
... | merged@(Node _ _ _ _ _) = Node min-key bot≤min-key min-val [ merged ]

¬heap[0] : ∀ {bot} → ¬ (Heap bot 0)
¬heap[0] ()
