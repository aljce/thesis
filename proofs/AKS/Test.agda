open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module AKS.Test where

open import Data.Unit using (tt)
open import Agda.Builtin.FromNat using (Number)
open import AKS.Nat

test = ⟅ 4 *⁺ 6 ⇓⟆

