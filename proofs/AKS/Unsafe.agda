{-# OPTIONS --with-K #-}
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality.WithK using (≡-erase)

-- acursed and unmentionable
-- turn back traveller
module AKS.Unsafe where

open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe) public

postulate
  TODO : ∀ {a} {A : Set a} → A
  BOTTOM : ∀ {a} {A : Set a} → A
  .irrelevance : ∀ {a} {A : Set a} -> .A -> A
  ≡-recomp : ∀ {a} {A : Set a} {x y : A} → .(x ≡ y) → x ≡ y
  fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

≡-recomputable : ∀ {a} {A : Set a} {x y : A} → .(x ≡ y) → x ≡ y
≡-recomputable x≡y = ≡-erase (≡-recomp x≡y)
