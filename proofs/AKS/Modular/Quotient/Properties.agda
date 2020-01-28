open import Level using (0ℓ)
open import Function using (_$_)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; isEquivalence; setoid; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)
open import Relation.Nullary.Negation using (contradiction)
open ≡-Reasoning

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.FromNat using (Number)

open import Data.Product using (_,_)

open import AKS.Primality using (IsPrime; Prime; bézout-prime)

module AKS.Modular.Quotient.Properties {P : Prime} where

open Prime P using () renaming (prime to p; isPrime to p-isPrime)
open IsPrime p-isPrime using (1<p)

open import AKS.Nat using (ℕ; zero; suc; _<_; _≤_; _∸_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≟_ to _≟ℕ_)
open import AKS.Nat using (<⇒≤; [n∸m]+m≡n; suc-mono-≤; *-mono-≤; ≤-refl)
import AKS.Nat as Nat
import Data.Nat.Properties as Nat
open import AKS.Nat.Divisibility using (_%_; %-distribˡ-+; %-distribˡ-∸; %-distribˡ-*; m%n%n≡m%n; n<m⇒n%m≡n; n%m<m; n%n≡0; 0%m≡0; 1%m≡1; [m+kn]%n≡m%n)
open import AKS.Nat.GCD using (+ʳ; +ˡ)
open import AKS.Modular.Quotient.Base using (ℤ/[_]; ℤ✓; mod; mod<p; module Operations)
open Operations {P} using ([_]; _+_; _*_; -_; _⁻¹; _/_; _≟_; p≢0; ℤ/[]-irrelevance; n≢0⇒mod[n]≢0)

open import Algebra.Structures {A = ℤ/[ P ]} _≡_ using
  ( IsCommutativeRing; IsRing; IsAbelianGroup
  ; IsGroup; IsMonoid; IsSemigroup; IsMagma
  )
open import Algebra.Definitions {A = ℤ/[ P ]} _≡_ using
  ( _DistributesOver_; _DistributesOverʳ_; _DistributesOverˡ_
  ; RightIdentity; LeftIdentity; Identity; Associative; Commutative
  ; RightInverse; LeftInverse; Inverse
  )
open import AKS.Algebra.Structures (ℤ/[ P ]) _≡_ using (IsNonZeroCommutativeRing; IsIntegralDomain; IsGCDDomain; IsDecField)
open import Algebra.Bundles using (Ring; CommutativeRing)
open import AKS.Algebra.Bundles using (NonZeroCommutativeRing; DecField)

open import AKS.Unsafe using (≢-irrelevant)

+-isMagma : IsMagma _+_
+-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong = cong₂ _+_
  }

mod≡mod%p : ∀ (x : ℤ/[ P ]) → mod x ≡ (mod x % p) {p≢0}
mod≡mod%p (ℤ✓ x x<p) = sym (n<m⇒n%m≡n x<p)

mod≡mod%p%p : ∀ (x : ℤ/[ P ]) → mod x ≡ ((mod x % p) {p≢0} % p) {p≢0}
mod≡mod%p%p x = begin
  mod x         ≡⟨ mod≡mod%p x ⟩
  mod x % p     ≡⟨ sym (m%n%n≡m%n (mod x) p) ⟩
  mod x % p % p ∎

+-assoc : Associative _+_
+-assoc x y z = ℤ/[]-irrelevance $ begin
  ((mod x +ℕ mod y) % p +ℕ mod z) % p             ≡⟨ cong₂ (λ a b → (a +ℕ b) % p) (%-distribˡ-+ (mod x) (mod y) p {p≢0}) (mod≡mod%p z) ⟩
  ((mod x % p +ℕ mod y % p) % p +ℕ mod z % p) % p ≡⟨ sym (%-distribˡ-+ (mod x % p +ℕ mod y % p) (mod z) p) ⟩
  ((mod x % p +ℕ mod y % p) +ℕ mod z) % p         ≡⟨ cong (λ a → (a % p) {p≢0}) (Nat.+-assoc (mod x % p) (mod y % p) (mod z)) ⟩
  (mod x % p +ℕ (mod y % p +ℕ mod z)) % p         ≡⟨ %-distribˡ-+ (mod x % p) (mod y % p +ℕ mod z) p ⟩
  (mod x % p % p +ℕ (mod y % p +ℕ mod z) % p) % p ≡⟨ cong₂ (λ a b → (a +ℕ (b +ℕ mod z) % p) % p) (sym (mod≡mod%p%p x)) (sym (mod≡mod%p y)) ⟩
  (mod x +ℕ (mod y +ℕ mod z) % p) % p ∎

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc = +-assoc
  }

+-comm : Commutative _+_
+-comm x y = ℤ/[]-irrelevance $ begin
  (mod x +ℕ mod y) % p ≡⟨ cong (λ a → (a % p) {p≢0}) (Nat.+-comm (mod x) (mod y)) ⟩
  (mod y +ℕ mod x) % p ∎

+-identityˡ : LeftIdentity 0 _+_
+-identityˡ x = ℤ/[]-irrelevance $ begin
  (0 % p +ℕ mod x) % p     ≡⟨ cong (λ a → (0 % p +ℕ a) % p) (mod≡mod%p x) ⟩
  (0 % p +ℕ mod x % p) % p ≡⟨ sym (%-distribˡ-+ 0 (mod x) p) ⟩
  (0 +ℕ mod x) % p         ≡⟨ sym (mod≡mod%p x) ⟩
  mod x                    ∎

open import Algebra.FunctionProperties.Consequences.Propositional using (comm+idˡ⇒idʳ; comm+invˡ⇒invʳ; comm+distrˡ⇒distrʳ)

+-identityʳ : RightIdentity 0 _+_
+-identityʳ = comm+idˡ⇒idʳ +-comm {0} +-identityˡ

+-identity : Identity 0 _+_
+-identity = +-identityˡ , +-identityʳ

+-isMonoid : IsMonoid _+_ 0
+-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity = +-identity
  }

-‿inverseˡ : LeftInverse 0 -_ _+_
-‿inverseˡ (ℤ✓ zero x<p) = refl
-‿inverseˡ (ℤ✓ (suc x) x<p) = ℤ/[]-irrelevance $ begin
  ((p ∸ suc x) +ℕ suc x) % p ≡⟨ cong (λ a → (a % p) {p≢0}) ([n∸m]+m≡n (<⇒≤ x<p)) ⟩
  p % p ≡⟨ n%n≡0 p ⟩
  0     ≡⟨ sym (0%m≡0 p {p≢0}) ⟩
  0 % p ∎

-‿inverseʳ : RightInverse 0 -_ _+_
-‿inverseʳ = comm+invˡ⇒invʳ {_⁻¹ = -_} +-comm -‿inverseˡ

-‿inverse : Inverse 0 -_ _+_
-‿inverse = -‿inverseˡ , -‿inverseʳ

+-isGroup : IsGroup _+_ 0 -_
+-isGroup = record
  { isMonoid = +-isMonoid
  ; inverse = -‿inverse
  ; ⁻¹-cong = cong -_
  }

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
*-assoc x y z = ℤ/[]-irrelevance $ begin
  ((mod x *ℕ mod y) % p *ℕ mod z) % p                   ≡⟨ cong₂ (λ a b → (a *ℕ b) % p) (%-distribˡ-* (mod x) (mod y) p {p≢0}) (mod≡mod%p z) ⟩
  (((mod x % p) *ℕ (mod y % p)) % p *ℕ (mod z % p)) % p ≡⟨ sym (%-distribˡ-* ((mod x % p) *ℕ (mod y % p)) (mod z) p) ⟩
  (((mod x % p) *ℕ (mod y % p)) *ℕ mod z) % p           ≡⟨ cong (λ a → (a % p) {p≢0}) (Nat.*-assoc (mod x % p) (mod y % p) (mod z)) ⟩
  ((mod x % p) *ℕ ((mod y % p) *ℕ mod z)) % p           ≡⟨ %-distribˡ-* (mod x % p) ((mod y % p) *ℕ mod z) p ⟩
  ((mod x % p % p) *ℕ (((mod y % p) *ℕ mod z) % p)) % p ≡⟨ cong₂ (λ a b → (a *ℕ ((b *ℕ mod z) % p)) % p) (sym (mod≡mod%p%p x)) (sym (mod≡mod%p y)) ⟩
  (mod x *ℕ ((mod y *ℕ mod z) % p)) % p ∎

*-isSemigroup : IsSemigroup _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc = *-assoc
  }

*-comm : Commutative _*_
*-comm x y = ℤ/[]-irrelevance $ begin
  (mod x *ℕ mod y) % p ≡⟨ cong (λ a → (a % p) {p≢0}) (Nat.*-comm (mod x) (mod y)) ⟩
  (mod y *ℕ mod x) % p ∎

*-identityˡ : LeftIdentity 1 _*_
*-identityˡ x = ℤ/[]-irrelevance $ begin
  (1 % p *ℕ mod x) % p ≡⟨ cong (λ a → ((a *ℕ mod x) % p) {p≢0}) (1%m≡1 1<p) ⟩
  (1 *ℕ mod x) % p     ≡⟨ cong (λ a → a % p) (Nat.*-identityˡ (mod x)) ⟩
  mod x % p            ≡⟨ sym (mod≡mod%p x) ⟩
  mod x                ∎

*-identityʳ : RightIdentity 1 _*_
*-identityʳ = comm+idˡ⇒idʳ *-comm {1} *-identityˡ

*-identity : Identity 1 _*_
*-identity = *-identityˡ , *-identityʳ

*-isMonoid : IsMonoid _*_ 1
*-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity = *-identity
  }

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ r x y = ℤ/[]-irrelevance $ begin
  (mod r *ℕ ((mod x +ℕ mod y) % p)) % p              ≡⟨ cong (λ a → (a *ℕ ((mod x +ℕ mod y) % p)) % p) (mod≡mod%p r) ⟩
  (mod r % p *ℕ ((mod x +ℕ mod y) % p)) % p          ≡⟨ sym (%-distribˡ-* (mod r) (mod x +ℕ mod y) p) ⟩
  (mod r *ℕ (mod x +ℕ mod y)) % p                    ≡⟨ cong (λ a → (a % p) {p≢0}) (Nat.*-distribˡ-+ (mod r) (mod x) (mod y)) ⟩
  (mod r *ℕ mod x +ℕ mod r *ℕ mod y) % p             ≡⟨ %-distribˡ-+ (mod r *ℕ mod x) (mod r *ℕ mod y) p ⟩
  ((mod r *ℕ mod x) % p +ℕ (mod r *ℕ mod y) % p) % p ∎

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ = comm+distrˡ⇒distrʳ {_} {_} {_*_} {_+_} *-comm *-distribˡ-+

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

+-*-isRing : IsRing _+_ _*_ -_ 0 1
+-*-isRing = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; *-isMonoid = *-isMonoid
  ; distrib = *-distrib-+
  }

+-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0 1
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

open import Data.Empty using (⊥)

0≢1 : [ 0 ] ≢ [ 1 ]
0≢1 [0]≡[1] = false
  where
  0≡1 : zero ≡ 1
  0≡1 = begin
    0     ≡⟨ sym (0%m≡0 p {p≢0}) ⟩
    0 % p ≡⟨ cong mod [0]≡[1] ⟩
    1 % p ≡⟨ 1%m≡1 1<p ⟩
    1     ∎
  false : ⊥
  false with 0≡1
  ... | ()

+-*-isNonZeroCommutativeRing : IsNonZeroCommutativeRing _+_ _*_ -_ 0 1
+-*-isNonZeroCommutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  ; 0#≉1# = 0≢1
  }

+-*-nonZeroCommutativeRing : NonZeroCommutativeRing 0ℓ 0ℓ
+-*-nonZeroCommutativeRing = record { isNonZeroCommutativeRing = +-*-isNonZeroCommutativeRing }

⁻¹-inverse-lemma₁ : ∀ (n : ℤ/[ P ]) x y → 1 +ℕ x *ℕ mod n ≡ y *ℕ p → ((mod n *ℕ (p ∸ (x % p) {p≢0})) % p) {p≢0} ≡ (1 % p) {p≢0}
⁻¹-inverse-lemma₁ n x y 1+x*n≡y*p = begin
  (mod n *ℕ (p ∸ x % p)) % p                             ≡⟨ cong (λ t → (t % p) {p≢0}) (Nat.*-distribˡ-∸ (mod n) p (x % p)) ⟩
  ((1 +ℕ mod n *ℕ p) ∸ (1 +ℕ mod n *ℕ (x % p))) % p     ≡⟨ %-distribˡ-∸ (1 +ℕ mod n *ℕ p) (1 +ℕ mod n *ℕ (x % p)) p 1+n*x%p≤1+n*p ⟩
  ((1 +ℕ mod n *ℕ p) ∸ (1 +ℕ mod n *ℕ (x % p)) % p) % p ≡⟨ cong (λ t → ((1 +ℕ mod n *ℕ p) ∸ t) % p) lemma ⟩
  ((1 +ℕ mod n *ℕ p) ∸ 0) % p                           ≡⟨ [m+kn]%n≡m%n 1 (mod n) p ⟩
  1 % p                                                  ∎
  where
  lemma : ((1 +ℕ mod n *ℕ (x % p) {p≢0}) % p) {p≢0} ≡ 0
  lemma = begin
    (1 +ℕ mod n *ℕ (x % p)) % p                 ≡⟨ cong (λ t → ((1 +ℕ t *ℕ (x % p) {p≢0}) % p) {p≢0}) (mod≡mod%p n) ⟩
    (1 +ℕ (mod n % p) *ℕ (x % p)) % p           ≡⟨ %-distribˡ-+ 1 ((mod n % p) *ℕ (x % p)) p ⟩
    (1 % p +ℕ ((mod n % p) *ℕ (x % p)) % p) % p ≡⟨ cong (λ t → (1 % p +ℕ t) % p) (sym (%-distribˡ-* (mod n) x p)) ⟩
    (1 % p +ℕ (mod n *ℕ x) % p) % p             ≡⟨ sym (%-distribˡ-+ 1 (mod n *ℕ x) p) ⟩
    (1 +ℕ mod n *ℕ x) % p                       ≡⟨ cong (λ t → ((1 +ℕ t) % p) {p≢0}) (Nat.*-comm (mod n) x) ⟩
    (1 +ℕ x *ℕ mod n) % p                       ≡⟨ cong (λ t → (t % p) {p≢0}) 1+x*n≡y*p ⟩
    (y *ℕ p) % p                                ≡⟨ [m+kn]%n≡m%n 0 y p ⟩
    0 % p                                       ≡⟨ 0%m≡0 p ⟩
    0 ∎
  1+n*x%p≤1+n*p : 1 +ℕ mod n *ℕ (x % p) {p≢0} ≤ 1 +ℕ mod n *ℕ p
  1+n*x%p≤1+n*p = suc-mono-≤ (*-mono-≤ {mod n} ≤-refl (<⇒≤ (n%m<m x p)))

⁻¹-inverse-lemma₂ : ∀ (n : ℤ/[ P ]) x y → 1 +ℕ y *ℕ p ≡ x *ℕ mod n → ((mod n *ℕ (x % p) {p≢0}) % p) {p≢0} ≡ (1 % p) {p≢0}
⁻¹-inverse-lemma₂ n x y 1+y*p≡x*n = begin
  (mod n *ℕ (x % p)) % p       ≡⟨ cong (λ t → (t *ℕ (x % p)) % p) (mod≡mod%p n) ⟩
  ((mod n % p) *ℕ (x % p)) % p ≡⟨ sym (%-distribˡ-* (mod n) x p) ⟩
  (mod n *ℕ x) % p             ≡⟨ cong (λ t → (t % p) {p≢0}) (Nat.*-comm (mod n) x) ⟩
  (x *ℕ mod n) % p             ≡⟨ cong (λ t → (t % p) {p≢0}) (sym 1+y*p≡x*n) ⟩
  (1 +ℕ y *ℕ p) % p            ≡⟨ [m+kn]%n≡m%n 1 y p ⟩
  1 % p ∎

⁻¹-inverse : ∀ n {n≢0} → n * (n ⁻¹) {n≢0} ≡ 1
⁻¹-inverse n {n≢0} with bézout-prime (mod n) p (n≢0⇒mod[n]≢0 n≢0) (mod<p n) p-isPrime
... | +ʳ x y 1+x*n≡y*p = ℤ/[]-irrelevance (⁻¹-inverse-lemma₁ n x y 1+x*n≡y*p)
... | +ˡ x y 1+y*p≡x*n = ℤ/[]-irrelevance (⁻¹-inverse-lemma₂ n x y 1+y*p≡x*n)

/-inverse : ∀ x y {y≢0} → x ≡ y * (x / y) {y≢0}
/-inverse x y {y≢0} = begin
  x                      ≡⟨ sym (*-identityʳ x) ⟩
  x * 1                  ≡⟨ cong (λ a → x * a) (sym (⁻¹-inverse y {y≢0})) ⟩
  x * (y * (y ⁻¹) {y≢0}) ≡⟨ sym (*-assoc x y ((y ⁻¹) {y≢0})) ⟩
  (x * y) * (y ⁻¹) {y≢0} ≡⟨ cong (λ a → a * (y ⁻¹) {y≢0}) (*-comm x y) ⟩
  (y * x) * (y ⁻¹) {y≢0} ≡⟨ *-assoc y x ((y ⁻¹) {y≢0}) ⟩
  y * (x / y) {y≢0} ∎

open import AKS.Algebra.Consequences +-*-nonZeroCommutativeRing using (module Inverse⇒Field)

open Inverse⇒Field _≟_ ≡-irrelevant ≢-irrelevant _/_ /-inverse
  using (gcd)
  renaming (isField to +-*-/-isField; [field] to +-*-/-field) public

+-*-/-isDecField : IsDecField _≟_ _+_ _*_ -_ 0 1 _/_ gcd
+-*-/-isDecField = record { isField = +-*-/-isField }

+-*-/-decField : DecField 0ℓ 0ℓ
+-*-/-decField = record { isDecField = +-*-/-isDecField }



