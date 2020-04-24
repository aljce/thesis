open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; False)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Antisymmetric; Irrelevant; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)
open ≡-Reasoning
open import Function using (_$_)

module AKS.Nat.GCD where

open import AKS.Nat.Base using (ℕ; _+_; _*_; zero; suc; _<_; _≤_; lte; _≟_; _∸_)
open import AKS.Nat.Properties using (≢⇒¬≟; ≤-antisym; <⇒≱)
open import Data.Nat.Properties using (*-distribʳ-∸; m+n∸n≡m)
open import AKS.Nat.Divisibility
  using (modₕ; _/_; _%_; n%m<m; m≡m%n+[m/n]*n; m%n≡m∸m/n*n; /-cancelʳ; Euclidean✓)
  renaming (_div_ to _ediv_)
open import Data.Nat.Properties using (*-+-commutativeSemiring; *-zeroʳ; +-comm; *-comm; *-assoc)
open import AKS.Algebra.Structures ℕ _≡_ using (module Modulus)
open import AKS.Algebra.Divisibility *-+-commutativeSemiring public

open import AKS.Unsafe using (≢-irrelevant)

auto-∣ : ∀ {d a} {{ d≢0 : False (d ≟ 0) }} {{ pf : True (a ≟ (a / d) {d≢0} * d)}} → d ∣ a
auto-∣ {d} {a} {{ d≢0 }} with a ≟ (a / d) {d≢0} * d
... | yes pf = divides (a / d) pf

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
mod-distribʳ-* c a b {b≢0} {b*c≢0} = begin
  (a * c) mod (b * c)                     ≡⟨ m%n≡m∸m/n*n (a * c) (b * c) ⟩
  (a * c) ∸ ((a * c) / (b * c)) * (b * c) ≡⟨ cong (λ x → a * c ∸ x) (sym (*-assoc ((a * c) / (b * c)) b c)) ⟩
  (a * c) ∸ (((a * c) / (b * c)) * b) * c ≡⟨ sym (*-distribʳ-∸ c a (((a * c) / (b * c)) * b)) ⟩
  (a ∸ ((a * c) / (b * c)) * b) * c       ≡⟨ cong (λ x → (a ∸ x * b) * c) (/-cancelʳ c a b) ⟩
  (a ∸ (a / b) * b) * c                   ≡⟨ cong (λ x → x * c) (sym (m%n≡m∸m/n*n a b)) ⟩
  a mod b * c                             ∎

open Euclidean (λ n → n) _div_ _mod_ _≟_ ≡-irrelevant ≢-irrelevant division modulus mod-cong mod-distribʳ-*
  using (gcdₕ; gcd; gcd-isGCD; Identity; +ʳ; +ˡ; Bézout; lemma; bézout) public

open IsGCD gcd-isGCD public

open GCD gcd-isGCD ∣-antisym
  using
    ( _⊥_; ⊥-sym; ⊥-respˡ; ⊥-respʳ
    ) public
  renaming
    ( gcd[a,1]≈1 to gcd[a,1]≡1
    ; gcd[1,a]≈1 to gcd[1,a]≡1
    ; a≉0⇒gcd[a,b]≉0 to a≢0⇒gcd[a,b]≢0
    ; b≉0⇒gcd[a,b]≉0 to b≢0⇒gcd[a,b]≢0
    ; gcd[0,a]≈a to gcd[0,a]≡a
    ; gcd[a,0]≈a to gcd[a,0]≡a
    ; gcd[0,a]≈1⇒a≈1 to gcd[0,a]≡1⇒a≡1
    ; gcd[a,0]≈1⇒a≈1 to gcd[a,0]≡1⇒a≡1
    ) public

∣n+m∣m⇒∣n : ∀ {i n m} → i ∣ n + m → i ∣ m → i ∣ n
∣n+m∣m⇒∣n {i} {n} {m} (divides q₁ n+m≡q₁*i) (divides q₂ m≡q₂*i) =
  divides (q₁ ∸ q₂) $ begin
    n               ≡⟨ sym (m+n∸n≡m n m) ⟩
    (n + m) ∸ m     ≡⟨ cong₂ (λ x y → x ∸ y) n+m≡q₁*i m≡q₂*i ⟩
    q₁ * i ∸ q₂ * i ≡⟨ sym (*-distribʳ-∸ i q₁ q₂) ⟩
    (q₁ ∸ q₂) * i   ∎

∣⇒≤ : ∀ {m n} {n≢0 : False (n ≟ 0)} → m ∣ n → m ≤ n
∣⇒≤ {m} {suc n} (divides (suc q) 1+n≡m+q*m) = lte (q * m) (sym 1+n≡m+q*m)

_∣?_ : Decidable _∣_
d ∣? a with d ≟ 0
d ∣? a | yes refl with a ≟ 0
d ∣? a | yes refl | yes refl = yes ∣-refl
d ∣? a | yes refl | no a≢0 = no λ 0∣a → contradiction (0∣n⇒n≈0 0∣a) a≢0
d ∣? a | no d≢0 with (a ediv d) {≢⇒¬≟ d≢0}
d ∣? a | no d≢0 | Euclidean✓ q r pf r<d with r ≟ 0
d ∣? a | no d≢0 | Euclidean✓ q r pf r<d | yes refl =
  yes $ divides q $ begin
    a ≡⟨ pf ⟩
    0 + d * q ≡⟨⟩
    d * q ≡⟨ *-comm d q ⟩
    q * d ∎
d ∣? a | no d≢0 | Euclidean✓ q r pf r<d | no r≢0 = no ¬d∣a
  where
  ¬d∣a : ¬ (d ∣ a)
  ¬d∣a d∣a = contradiction d≤r (<⇒≱ r<d)
    where
    d∣r+d*q : d ∣ r + d * q
    d∣r+d*q = ∣-respʳ pf d∣a

    d∣r : d ∣ r
    d∣r = ∣n+m∣m⇒∣n d∣r+d*q (∣n⇒∣n*m _ _ _ ∣-refl)

    d≤r : d ≤ r
    d≤r = ∣⇒≤ {n≢0 = ≢⇒¬≟ r≢0} d∣r
