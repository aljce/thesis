open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality.WithK using (≡-erase)

-- acursed and unmentionable
-- turn back traveller
module Unsafe where

postulate
  TODO : ∀ {a} {A : Set a} → A
  .irrelevance : ∀ {a} {A : Set a} -> .A -> A
  ≡-recomp : ∀ {a} {A : Set a} {x y : A} → .(x ≡ y) → x ≡ y

≡-recomputable : ∀ {a} {A : Set a} {x y : A} → .(x ≡ y) → x ≡ y
≡-recomputable x≡y = ≡-erase (≡-recomp x≡y)

EVIL = TODO