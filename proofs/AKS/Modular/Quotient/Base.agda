open import Relation.Nullary.Decidable using (False; map)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Function.Equivalence as FE using ()

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.FromNat using (Number)

module AKS.Modular.Quotient.Base where

open import AKS.Nat using (ℕ; zero; suc; _<_; _∸_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≟_ to _≟ℕ_)
open import AKS.Nat using (≢⇒¬≟; ∸-mono-<ʳ; 0<1+n; <⇒≤; <-irrelevant; 0≢⇒0<)
open import AKS.Nat.Divisibility using (_%_; n%m<m; 0%m≡0; 1%m≡1; [m+kn]%n≡m%n; m%n%n≡m%n; %-distribˡ-+; %-distribˡ-*)
open import AKS.Nat.GCD using (+ʳ; +ˡ)
open import AKS.Primality using (IsPrime; Prime; prime≢0; bézout-prime)
open Prime

record ℤ/[_] (P : Prime) : Set where
  constructor ℤ✓
  field
    mod : ℕ
    mod<p : mod < prime P
open ℤ/[_] public

module Operations {P : Prime} where
  open Prime P using () renaming (prime to p; isPrime to p-isPrime)
  open IsPrime p-isPrime using (1<p)

  p≢0 : False (p ≟ℕ 0)
  p≢0 = ≢⇒¬≟ (prime≢0 p-isPrime)

  [_] : ℕ → ℤ/[ P ]
  [ n ] = ℤ✓ ((n % p) {p≢0}) (n%m<m n p)

  instance
    ℤ/[]-number : Number (ℤ/[ P ])
    ℤ/[]-number = record
      { Constraint = λ _ → ⊤
      ; fromNat = λ n → [ n ]
      }

  infixl 6 _+_
  _+_ : ℤ/[ P ] → ℤ/[ P ] → ℤ/[ P ]
  n + m = [ mod n +ℕ mod m ]

  infix 8 -_
  -_ : ℤ/[ P ] → ℤ/[ P ]
  - (ℤ✓ zero    0<p) = ℤ✓ zero  0<p
  - (ℤ✓ (suc n) 1+n<p) = ℤ✓ (p ∸ suc n) (∸-mono-<ʳ (<⇒≤ 1+n<p) 0<1+n)

  infixl 7 _*_
  _*_ : ℤ/[ P ] → ℤ/[ P ] → ℤ/[ P ]
  n * m = [ mod n *ℕ mod m ]

  ℤ/[]-irrelevance : ∀ {x y : ℤ/[ P ]} → mod x ≡ mod y → x ≡ y
  ℤ/[]-irrelevance {ℤ✓ mod[x] mod[x]<p} {ℤ✓ .mod[x] mod[y]<p} refl = cong (λ z<p → ℤ✓ mod[x] z<p) (<-irrelevant mod[x]<p mod[y]<p)

  n≢0⇒mod[n]≢0 : ∀ {n} → n ≢ 0 → mod n ≢ 0
  n≢0⇒mod[n]≢0 {ℤ✓ zero _} n≢0 = contradiction (ℤ/[]-irrelevance (sym (0%m≡0 p))) n≢0
  n≢0⇒mod[n]≢0 {ℤ✓ (suc n) _} n≢0 = λ ()

  bézout-x∤p : ∀ n x y → 1 +ℕ x *ℕ n ≡ y *ℕ p → 0 ≢ (x % p) {p≢0}
  bézout-x∤p n x y 1+x*n≡y*p 0≡x%p = contradiction 1≡0 (λ ())
    where
    1≡0 : 1 ≡ zero
    1≡0 = begin
      1 ≡⟨ sym (1%m≡1 1<p) ⟩
      (1 +ℕ 0 *ℕ n) % p ≡⟨ cong (λ t → ((1 +ℕ t *ℕ n) % p) {p≢0}) 0≡x%p ⟩
      (1 +ℕ (x % p) *ℕ n) % p ≡⟨ %-distribˡ-+ 1 ((x % p) *ℕ n) p ⟩
      (1 % p +ℕ ((x % p) *ℕ n) % p) % p ≡⟨ cong (λ t → ((1 % p +ℕ t) % p) {p≢0}) (%-distribˡ-* (x % p) n p) ⟩
      (1 % p +ℕ ((x % p % p) *ℕ (n % p)) % p) % p ≡⟨ cong (λ t → (1 % p +ℕ (t *ℕ (n % p)) % p) % p) (m%n%n≡m%n x p) ⟩
      (1 % p +ℕ ((x % p) *ℕ (n % p)) % p) % p ≡⟨ cong (λ t → (1 % p +ℕ t) % p) (sym (%-distribˡ-* x n p)) ⟩
      (1 % p +ℕ (x *ℕ n) % p) % p ≡⟨ sym (%-distribˡ-+ 1 (x *ℕ n) p) ⟩
      (1 +ℕ x *ℕ n) % p ≡⟨ cong (λ t → (t % p) {p≢0}) 1+x*n≡y*p ⟩
      (y *ℕ p) % p ≡⟨ [m+kn]%n≡m%n 0 y p {p≢0} ⟩
      0 % p ≡⟨ 0%m≡0 p ⟩
      0 ∎

  -- x⁻¹ * x - 1 ≡ z * p
  infix 8 _⁻¹
  _⁻¹ : ∀ (n : ℤ/[ P ]) {n≢0 : n ≢ 0} → ℤ/[ P ]
  (n ⁻¹) {n≢0} with bézout-prime (mod n) p (n≢0⇒mod[n]≢0 n≢0) (mod<p n) p-isPrime
  ... | +ʳ x y 1+x*n≡y*p = ℤ✓ (p ∸ (x % p) {p≢0}) (∸-mono-<ʳ (<⇒≤ (n%m<m x p)) (0≢⇒0< (bézout-x∤p (mod n) x y 1+x*n≡y*p)))
  ... | +ˡ x y 1+y*p≡x*n = [ x ]

  infixl 7 _/_
  _/_ : ∀ (n m : ℤ/[ P ]) {m≢0 : m ≢ 0} → ℤ/[ P ]
  (n / m) {m≢0} = n * (m ⁻¹) {m≢0}

  _≟_ : Decidable {A = ℤ/[ P ]} _≡_
  ℤ✓ x x<p ≟ ℤ✓ y y<p = map (FE.equivalence ℤ/[]-irrelevance (λ { refl → refl })) (x ≟ℕ y)

open Operations public
