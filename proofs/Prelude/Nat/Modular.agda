open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; isEquivalence; module ≡-Reasoning)
open ≡-Reasoning

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.FromNeg using (Negative)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)

module Prelude.Nat.Modular where

open import Data.Nat.DivMod using (%-distribˡ-+) renaming (_%_ to _%ℕ_)
open import Prelude.Nat using (ℕ; _<_; lte; ℕ-number) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _∸_ to _∸ℕ_)
open ℕ
open import Prelude.Nat using (∸-mono-<ʳ; 0<1+n; n<1+n; <-trans; <-irrelevant)
open import Prelude.Nat using (n%m<m; ≢⇒¬≟; n<m⇒n%m≡n)
import Data.Nat.Properties as Nat using (+-assoc)
open import Prelude.Primality using (Prime; Prime✓; IsPrime; IsPrime✓; prime≢0)
open Prime

record ℤ/[_] (P : Prime) : Set where
  constructor ℤ✓
  field
    mod : ℕ
    mod<p : mod < prime P
open ℤ/[_]

[_] : ∀ ℕ → ∀ {P} → ℤ/[ P ]
[ x ] {Prime✓ p p-isPrime} = ℤ✓ ((x %ℕ p) {¬p≟0}) (n%m<m x p {¬p≟0})
  where
  ¬p≟0 = ≢⇒¬≟ (prime≢0 p-isPrime)

ℤ✓-cong : ∀ {P : Prime} {x y : ℤ/[ P ]} → mod x ≡ mod y → x ≡ y
ℤ✓-cong {P} {ℤ✓ x x<p} {ℤ✓ .x y<p} refl = cong (ℤ✓ x) (<-irrelevant x<p y<p)

module _ {P : Prime} where
  open import Algebra.Structures {A = ℤ/[ P ]} _≡_ using (IsCommutativeRing; IsRing; IsAbelianGroup; IsGroup; IsMonoid; IsSemigroup; IsMagma)
  open import Algebra.Definitions {A = ℤ/[ P ]} _≡_ using (_DistributesOver_; RightIdentity; LeftIdentity; Identity; Associative; Commutative; RightInverse; LeftInverse; Inverse)

  open Prime P using () renaming (prime to p; isPrime to p-isPrime)

  ¬p≟0 = ≢⇒¬≟ (prime≢0 p-isPrime)

  instance
    ℤ/[p]-number : Number (ℤ/[ P ])
    ℤ/[p]-number = record
      { Constraint = λ _ → ⊤
      ; fromNat = λ n → [ n ]
      }

  infixl 6 _+_
  _+_ : ℤ/[ P ] → ℤ/[ P ] → ℤ/[ P ]
  x + y = [ mod x +ℕ mod y  ]

  infixl 7 _*_
  _*_ : ℤ/[ P ] → ℤ/[ P ] → ℤ/[ P ]
  x * y = [ mod x *ℕ mod y ]

  infixl 6 -_
  -_ : ℤ/[ P ] → ℤ/[ P ]
  - ℤ✓ zero _ = 0
  - ℤ✓ (suc x) 1+x<p = ℤ✓ (p ∸ℕ suc x) (∸-mono-<ʳ (<-trans n<1+n 1+x<p) 0<1+n)

  instance
    ℤ/[p]-negative : Negative (ℤ/[ P ])
    ℤ/[p]-negative = record
      { Constraint = λ _ → ⊤
      ; fromNeg = λ n → - [ n ]
      }

  test : ℤ/[ P ]
  test = 2 + -1 * 10

  open import Prelude.Unsafe using (TODO)

  infixl 7 _⁻¹
  _⁻¹ : ℤ/[ P ] → ℤ/[ P ]
  x ⁻¹ = TODO

  +-isMagma : IsMagma _+_
  +-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong = cong₂ _+_
    }

  mod[x]≡mod[x]%p : ∀ (x : ℤ/[ P ]) → mod x ≡ (mod x %ℕ p) {¬p≟0}
  mod[x]≡mod[x]%p (ℤ✓ x x<p) = sym (n<m⇒n%m≡n x<p)

  +-assoc : Associative _+_
  +-assoc x y z = ℤ✓-cong $ begin
    ((((mod x +ℕ mod y) %ℕ p) +ℕ mod z) %ℕ p)    ≡⟨ cong (λ t → (((mod x +ℕ mod y) %ℕ p) +ℕ t) %ℕ p) (mod[x]≡mod[x]%p z) ⟩
    (((mod x +ℕ mod y) %ℕ p +ℕ mod z %ℕ p) %ℕ p) ≡⟨ sym (%-distribˡ-+ (mod x +ℕ mod y) (mod z) p {¬p≟0}) ⟩
    ((mod x +ℕ mod y +ℕ mod z) %ℕ p)             ≡⟨ cong (λ t → (t %ℕ p) {¬p≟0}) (Nat.+-assoc (mod x) (mod y) (mod z)) ⟩
    ((mod x +ℕ (mod y +ℕ mod z)) %ℕ p)           ≡⟨ %-distribˡ-+ (mod x) (mod y +ℕ mod z) p {¬p≟0} ⟩
    ((mod x %ℕ p +ℕ (mod y +ℕ mod z) %ℕ p) %ℕ p) ≡⟨ cong (λ t → (t +ℕ (mod y +ℕ mod z) %ℕ p) %ℕ p) (sym (mod[x]≡mod[x]%p x)) ⟩
    (mod x +ℕ (mod y +ℕ mod z) %ℕ p) %ℕ p        ∎

  +-isSemigroup : IsSemigroup _+_
  +-isSemigroup = record
    { isMagma = +-isMagma
    ; assoc = +-assoc
    }

  +-identityˡ : LeftIdentity 0 _+_
  +-identityˡ x = ℤ✓-cong $ begin
    (mod 0 +ℕ mod x) %ℕ p ≡⟨ cong (λ t → ((t +ℕ mod x) %ℕ p) {¬p≟0}) TODO ⟩
    mod x %ℕ p ≡⟨ sym (mod[x]≡mod[x]%p x) ⟩
    mod x ∎

  +-identityʳ : RightIdentity 0 _+_
  +-identityʳ = TODO

  +-identity : Identity 0 _+_
  +-identity = +-identityˡ , +-identityʳ

  +-isMonoid : IsMonoid _+_ 0
  +-isMonoid = record
    { isSemigroup = +-isSemigroup
    ; identity = +-identity
    }

  +-inverseˡ : LeftInverse 0 -_ _+_
  +-inverseˡ = TODO

  +-inverseʳ : RightInverse 0 -_ _+_
  +-inverseʳ = TODO

  +-inverse : Inverse 0 -_ _+_
  +-inverse = +-inverseˡ , +-inverseʳ

  +-isGroup : IsGroup _+_ 0 -_
  +-isGroup = record
    { isMonoid = +-isMonoid
    ; inverse = +-inverse
    ; ⁻¹-cong = cong -_
    }

  +-comm : Commutative _+_
  +-comm = TODO

  +-isAbelianGroup : IsAbelianGroup _+_ 0 -_
  +-isAbelianGroup = record
    { isGroup = +-isGroup
    ; comm = +-comm
    }

  *-isMagma : IsMagma _*_
  *-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong = cong₂ _*_
    }

  *-assoc : Associative _*_
  *-assoc x y z = TODO

  *-isSemigroup : IsSemigroup _*_
  *-isSemigroup = record
    { isMagma = *-isMagma
    ; assoc = *-assoc
    }

  *-identityˡ : LeftIdentity 1 _*_
  *-identityˡ = TODO

  *-identityʳ : RightIdentity 1 _*_
  *-identityʳ = TODO

  *-identity : Identity 1 _*_
  *-identity = *-identityˡ , *-identityʳ

  *-1-isMonoid : IsMonoid _*_ 1
  *-1-isMonoid = record
    { isSemigroup = *-isSemigroup
    ; identity = *-identity
    }

  *-distrib-+ : _*_ DistributesOver _+_
  *-distrib-+ = TODO

  +-*-isRing : IsRing _+_ _*_ -_ 0 1
  +-*-isRing = record
    { +-isAbelianGroup = +-isAbelianGroup
    ; *-isMonoid = *-1-isMonoid
    ; distrib = *-distrib-+
    }

  *-comm : Commutative _*_
  *-comm = TODO

  +-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0 1
  +-*-isCommutativeRing = record
    { isRing = +-*-isRing
    ; *-comm = *-comm
    }
