open import Relation.Nullary.Decidable using (False)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Relation.Binary.PropositionalEquality.WithK using (≡-erase)

module AKS.Nat.Divisibility where

open import Data.Nat.Divisibility using (_∣_) public
open import Agda.Builtin.Nat using () renaming (mod-helper to modₕ; div-helper to divₕ) public
open import Data.Nat.DivMod using (_/_; _%_; %-distribˡ-+) public
open import Data.Nat.DivMod.Core using (a≤n⇒a[modₕ]n≡a)
open import Data.Nat.DivMod using (/-congˡ; /-congʳ) renaming (m≡m%n+[m/n]*n to div-lemma)

open import AKS.Nat.Base using (ℕ; _+_; _*_; _∸_; _≟_; lte; _≤_; _<_)
open ℕ
open import AKS.Nat.Properties using (+-suc)
open import AKS.Nat.Properties using (m≤m+n; m≤n+m; suc-mono-≤; ∸-mono-≤ˡ; +-lower-≤; ≤-refl; ≢⇒¬≟; module ≤-Reasoning)
open import AKS.Nat.Properties using (*-comm; +-identityʳ)
open ≤-Reasoning
import Data.Nat.DivMod as Nat
import Data.Nat.Properties as Nat
open import Data.Nat.Properties using (*-zeroʳ)

open import Polynomial.Simple.AlmostCommutativeRing.Instances using (module Nat)
open import Polynomial.Simple.Reflection using (solve)

a[modₕ]n≤n : ∀ acc d n → modₕ acc (acc + n) d n ≤ acc + n
a[modₕ]n≤n acc zero n = m≤m+n
a[modₕ]n≤n acc (suc d) zero = a[modₕ]n≤n zero d (acc + 0)
a[modₕ]n≤n acc (suc d) (suc n) rewrite +-suc acc n = a[modₕ]n≤n (suc acc) d n

n%m<m : ∀ n m {≢0 : False (m ≟ 0)} → (n % m) {≢0} < m
n%m<m n (suc m) = suc-mono-≤ (a[modₕ]n≤n 0 n m)

a[modₕ]n≤a : ∀ acc a n → modₕ acc (acc + n) a n ≤ acc + a
a[modₕ]n≤a acc zero n rewrite +-identityʳ acc = ≤-refl
a[modₕ]n≤a acc (suc a) (suc n) = begin
  modₕ acc (acc + suc n) (suc a) (suc n) ≡⟨ cong (λ v → modₕ acc v (suc a) (suc n)) (+-suc acc n) ⟩
  modₕ acc (suc acc + n) (suc a) (suc n) ≤⟨ a[modₕ]n≤a (suc acc) a n ⟩
  suc acc + a                            ≡⟨ sym (+-suc acc a) ⟩
  acc + suc a                            ∎
a[modₕ]n≤a acc (suc a) zero    = begin
  modₕ acc (acc + 0) (suc a) 0 ≡⟨ cong (λ v → modₕ acc v (suc a) 0) (+-identityʳ acc) ⟩
  modₕ acc acc (suc a) 0       ≤⟨ a[modₕ]n≤a 0 a acc ⟩
  a                            ≤⟨ m≤n+m ⟩
  suc a                        ≤⟨ m≤n+m ⟩
  acc + suc a                  ∎

n%m≤n : ∀ n m {≢0} → (n % m) {≢0} ≤ n
n%m≤n n (suc m) = a[modₕ]n≤a 0 n m

n<m⇒n%m≡n : ∀ {n m} {≢0 : False (m ≟ 0)} → n < m → (n % m) {≢0} ≡ n
n<m⇒n%m≡n {n} {suc m} (lte k refl) = ≡-erase (a≤n⇒a[modₕ]n≡a 0 (n + k) n k)

0%m≡0 : ∀ m {≢0 : False (m ≟ 0)} → (0 % m) {≢0} ≡ 0
0%m≡0 (suc m) = refl

1%m≡1 : ∀ {m} {≢0} → 1 < m → (1 % m) {≢0} ≡ 1
1%m≡1 {suc (suc m)} 1<m = refl

record Euclidean (n : ℕ) (m : ℕ) : Set where
  constructor Euclidean✓
  field
    q : ℕ
    r : ℕ
    division : n ≡ r + m * q
    r<m : r < m

m≡m%n+[m/n]*n : ∀ m n {n≢0 : False (n ≟ 0)} → m ≡ (m % n) {n≢0} + (m / n) {n≢0} * n
m≡m%n+[m/n]*n m (suc n) = div-lemma m n

m%n≡m∸m/n*n : ∀ m n {n≢0 : False (n ≟ 0)} → (m % n) {n≢0} ≡ m ∸ (m / n) {n≢0} * n
m%n≡m∸m/n*n m (suc n) = Nat.m%n≡m∸m/n*n m n

m%n%n≡m%n : ∀ m n {n≢0 : False (n ≟ 0)} → ((m % n) {n≢0} % n) {n≢0} ≡ (m % n) {n≢0}
m%n%n≡m%n m (suc n) = Nat.m%n%n≡m%n m n

n%n≡0 : ∀ n {n≢0 : False (n ≟ 0)} → (n % n) {n≢0} ≡ 0
n%n≡0 (suc n) = Nat.n%n≡0 n

[m+kn]%n≡m%n : ∀ m k n {n≢0 : False (n ≟ 0)} → ((m + k * n) % n) {n≢0} ≡ (m % n) {n≢0}
[m+kn]%n≡m%n m k (suc n) = Nat.[m+kn]%n≡m%n m k n

%-distribˡ-* : ∀ m n d {≢0} → ((m * n) % d) {≢0} ≡ (((m % d) {≢0} * (n % d) {≢0}) % d) {≢0}
%-distribˡ-* m n (suc d) = begin-equality
  (m * n) % suc d                                                           ≡⟨ cong (λ x → (x * n) % suc d) (m≡m%n+[m/n]*n m (suc d)) ⟩
  ((m % suc d + m / suc d * suc d) * n) % suc d                             ≡⟨ cong (λ x → x % suc d) (Nat.*-distribʳ-+ n (m % suc d) (m / suc d * suc d)) ⟩
  ((m % suc d) * n + (m / suc d * suc d) * n) % suc d                       ≡⟨ cong (λ x → ((m % suc d) * n + x) % suc d) (lemma (m / suc d) (suc d) n) ⟩
  ((m % suc d) * n + (m / suc d * n) * suc d) % suc d                       ≡⟨ Nat.[m+kn]%n≡m%n ((m % suc d) * n) (m / suc d * n) d ⟩
  ((m % suc d) * n) % suc d                                                 ≡⟨ cong (λ x → ((m % suc d) * x) % suc d) (m≡m%n+[m/n]*n n (suc d)) ⟩
  ((m % suc d) * (n % suc d + n / suc d * suc d)) % suc d                   ≡⟨ cong (λ x → x % suc d) (Nat.*-distribˡ-+ (m % suc d) (n % suc d) (n / suc d * suc d)) ⟩
  ((m % suc d) * (n % suc d) + (m % suc d) * (n / suc d * suc d)) % suc d   ≡⟨ cong (λ x → ((m % suc d) * (n % suc d) + x) % suc d) (sym (Nat.*-assoc (m % suc d) (n / suc d) (suc d))) ⟩
  ((m % suc d) * (n % suc d) + ((m % suc d) * (n / suc d)) * suc d) % suc d ≡⟨ Nat.[m+kn]%n≡m%n ((m % suc d) * (n % suc d)) ((m % suc d) * (n / suc d)) d ⟩
  ((m % suc d) * (n % suc d)) % suc d                                       ∎
  where
  lemma : ∀ x y z → (x * y) * z ≡ (x * z) * y
  lemma = solve Nat.ring

[m∸n]%n≡m%n : ∀ m n {n≢0 : False (n ≟ 0)} → n ≤ m → ((m ∸ n) % n) {n≢0} ≡ (m % n) {n≢0}
[m∸n]%n≡m%n (suc .(n + k)) (suc n) (lte k refl) = begin-equality
  ((suc n + k) ∸ suc n) % suc n ≡⟨ cong (λ t → t % suc n) (Nat.m+n∸m≡n (suc n) k) ⟩
  k % suc n                     ≡⟨ sym (Nat.[m+n]%n≡m%n k n) ⟩
  (k + suc n) % suc n           ≡⟨ cong (λ t → t % suc n) (Nat.+-comm k (suc n)) ⟩
  (suc n + k) % suc n           ∎

[m∸kn]%n≡m%n : ∀ m k n {n≢0 : False (n ≟ 0)} → k * n ≤ m → ((m ∸ k * n) % n) {n≢0} ≡ (m % n) {n≢0}
[m∸kn]%n≡m%n m zero (suc n) n≤m = refl
[m∸kn]%n≡m%n m (suc k) (suc n) k*n≤m = begin-equality
  (m ∸ (suc n + k * suc n)) % suc n ≡⟨ cong (λ t → t % suc n) (sym (Nat.∸-+-assoc m (suc n) (k * suc n)))  ⟩
  ((m ∸ suc n) ∸ k * suc n) % suc n ≡⟨ [m∸kn]%n≡m%n (m ∸ suc n) k (suc n) k*n≤m∸n ⟩
  (m ∸ suc n) % suc n               ≡⟨ [m∸n]%n≡m%n m (suc n) (+-lower-≤ (k * suc n) k*n≤m) ⟩
  m % suc n                         ∎
  where
  k*n≤m∸n : k * suc n ≤ m ∸ suc n
  k*n≤m∸n = begin
    k * suc n                   ≡⟨ sym (Nat.m+n∸m≡n (suc n) (k * suc n)) ⟩
    (suc n + k * suc n) ∸ suc n ≤⟨ ∸-mono-≤ˡ {suc n} m≤m+n k*n≤m ⟩
    m ∸ suc n                   ∎

%-distribˡ-∸ : ∀ m n d {≢0} → n ≤ m → ((m ∸ n) % d) {≢0} ≡ ((m ∸ (n % d) {≢0}) % d) {≢0}
%-distribˡ-∸ m n (suc d) n≤m = begin-equality
  (m ∸ n) % suc d                               ≡⟨ cong (λ t → (m ∸ t) % suc d) (m≡m%n+[m/n]*n n (suc d)) ⟩
  (m ∸ (n % suc d + n / suc d * suc d)) % suc d ≡⟨ cong (λ t → t % suc d) (sym (Nat.∸-+-assoc m (n % suc d) (n / suc d * suc d))) ⟩
  ((m ∸ n % suc d) ∸ n / suc d * suc d) % suc d ≡⟨ [m∸kn]%n≡m%n (m ∸ n % suc d) (n / suc d) (suc d) n/d*d≤m∸n%d ⟩
  (m ∸ n % suc d) % suc d                       ∎
  where
  n/d*d≤m∸n%d : n / suc d * suc d ≤ m ∸ n % suc d
  n/d*d≤m∸n%d = begin
    n / suc d * suc d                           ≡⟨ sym (Nat.m+n∸m≡n (n % suc d) (n / suc d * suc d)) ⟩
    (n % suc d + n / suc d * suc d) ∸ n % suc d ≡⟨ cong (λ t → t ∸ n % suc d) (sym (m≡m%n+[m/n]*n n (suc d))) ⟩
    n ∸ n % suc d                               ≤⟨ ∸-mono-≤ˡ {n % suc d} (n%m≤n n (suc d)) n≤m ⟩
    m ∸ n % suc d                               ∎

open import AKS.Unsafe using (trustMe)

/-cancelˡ : ∀ c a b {b≢0} {b*c≢0} → ((c * a) / (c * b)) {b*c≢0} ≡ (a / b) {b≢0}
/-cancelˡ (suc c) a (suc b) {b≢0} {b*c≢0} = trustMe

/-cancelʳ : ∀ c a b {b≢0} {b*c≢0} → ((a * c) / (b * c)) {b*c≢0} ≡ (a / b) {b≢0}
/-cancelʳ c a b {b≢0} {b*c≢0} = begin-equality
  (a * c) / (b * c) ≡⟨ /-congˡ {o≢0 = b*c≢0} (*-comm a c) ⟩
  (c * a) / (b * c) ≡⟨ /-congʳ (*-comm b c) ⟩
  (c * a) / (c * b) ≡⟨ /-cancelˡ c a b {b≢0} {c*b≢0} ⟩
  a / b ∎
  where
  c*b≢0 : False (c * b ≟ 0)
  c*b≢0 rewrite *-comm b c = b*c≢0

_div_ : ∀ n m {≢0 : False (m ≟ 0)} → Euclidean n m
n div suc m = Euclidean✓ (n / suc m) (n % suc m) (≡-erase div-proof) (n%m<m n (suc m))
  where
  div-proof : n ≡ n % suc m + suc m * (n / suc m)
  div-proof rewrite *-comm (suc m) (n / suc m) = m≡m%n+[m/n]*n n (suc m)



