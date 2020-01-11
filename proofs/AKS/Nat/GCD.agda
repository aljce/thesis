open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Antisymmetric; Irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)
open ≡-Reasoning

module AKS.Nat.GCD where

open import AKS.Nat.Base using (ℕ; _+_; _*_; zero; suc; _<_; lte; _≟_; _∸_)
open import AKS.Nat.Properties using (≢⇒¬≟; ≤-antisym)
open import AKS.Nat.Divisibility using (modₕ; _/_; _%_; n%m<m; m≡m%n+[m/n]*n)
open import Data.Nat.Properties using (*-+-commutativeSemiring; *-zeroʳ; +-comm; *-comm)
open import AKS.Algebra.Structures ℕ _≡_ using (module Modulus)
open import AKS.Algebra.Divisibility *-+-commutativeSemiring public

open import AKS.Unsafe using (TODO; ≢-irrelevant)

∣-antisym : Antisymmetric _≡_ _∣_
∣-antisym {x} {y} (divides zero refl) (divides q₂ refl) = *-zeroʳ q₂
∣-antisym {x} {y} (divides (suc q₁) refl) (divides zero refl) = sym (*-zeroʳ (suc q₁))
∣-antisym {x} {y} (divides (suc q₁) refl) (divides (suc q₂) pf₂) = ≤-antisym (lte (q₁ * x) refl) (lte (q₂ * y) (sym pf₂))

-- The euclidean norm is just the identity function on ℕ
∣_∣ : ∀ n {n≉0 : n ≢ 0} → ℕ
∣ n ∣ = n

_div_ : ∀ (n m : ℕ) {m≢0 : m ≢ 0} → ℕ
(n div m) {m≢0} = (n / m) {≢⇒¬≟ m≢0}

_mod_ : ∀ (n m : ℕ) {m≢0 : m ≢ 0} → ℕ
(n mod m) {m≢0} = (n % m) {≢⇒¬≟ m≢0}

division : ∀ n m {m≢0 : m ≢ 0} → n ≡ m * (n div m) {m≢0} + (n mod m) {m≢0}
division n m {m≢0} = begin
  n                                     ≡⟨ m≡m%n+[m/n]*n n m {≢⇒¬≟ m≢0} ⟩
  (n % m) + (n / m) * m                 ≡⟨ +-comm (n % m) (n / m * m) ⟩
  (n / m) * m + (n % m)                 ≡⟨ cong (λ t → t + (n % m) {≢⇒¬≟ m≢0}) (*-comm (n / m) m) ⟩
  m * (n div m) {m≢0} + (n mod m) {m≢0} ∎

open Modulus 0 ∣_∣ _mod_

modulus : ∀ n m {m≢0} → Remainder n m {m≢0}
modulus n m {m≢0} with (n mod m) {m≢0} ≟ 0
... | yes r≡0 = 0≈ r≡0
... | no  r≢0 = 0≉ r≢0 (n%m<m n m)

mod-cong : ∀ {x₁ x₂} {y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → ∀ {y₁≉0 y₂≉0} → (x₁ mod y₁) {y₁≉0} ≡ (x₂ mod y₂) {y₂≉0}
mod-cong refl refl {y₁≢0} {y₂≢0} rewrite ≢-irrelevant y₁≢0 y₂≢0 = refl

mod-distribʳ-* : ∀ c a b {b≢0} {b*c≢0} → ((a * c) mod (b * c)) {b*c≢0} ≡ (a mod b) {b≢0} * c
mod-distribʳ-* c a b {b≢0} {b*c≢0} = TODO

open Euclidean (λ n → n) _div_ _mod_ _≟_ ≡-irrelevant ≢-irrelevant division modulus mod-cong mod-distribʳ-*
  using (gcd; gcd-isGCD; Identity; +ʳ; +ˡ; Bézout; lemma; bézout) public

open GCD gcd-isGCD ∣-antisym
  using
    ( _⊥_; ⊥-sym; ⊥-respˡ; ⊥-respʳ
    ) public
  renaming
    ( gcd[a,1]≈1 to gcd[a,1]≡1
    ; a≉0⇒gcd[a,b]≉0 to a≢0⇒gcd[a,b]≢0
    ; b≉0⇒gcd[a,b]≉0 to b≢0⇒gcd[a,b]≢0
    ; gcd[0,a]≈a to gcd[0,a]≡a
    ; gcd[a,0]≈a to gcd[a,0]≡a
    ; gcd[0,a]≈1⇒a≈1 to gcd[0,a]≡1⇒a≡1
    ; gcd[a,0]≈1⇒a≈1 to gcd[a,0]≡1⇒a≡1
    ) public
