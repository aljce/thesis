open import Function using (_$_)

open import Data.Empty using (⊥-elim)

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)

open import Relation.Nullary.Decidable using (False)
open import Relation.Binary using (Antisymmetric)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; module ≡-Reasoning)
open ≡-Reasoning

module AKS.Nat.GCD where

open import AKS.Nat.Base using (ℕ; _+_; _*_; zero; suc; _<_; lte; _≟_; _∸_)
open import AKS.Nat.Divisibility using (modₕ; _/_; _%_; n%m<m; m≡m%n+[m/n]*n)
open import AKS.Nat.WellFounded using (Acc; acc; <-well-founded)
open import AKS.Nat.Properties using (≢⇒¬≟; <-irrefl; 0<1+n; ≤-antisym)
open import Data.Nat.Properties using (*-+-semiring; *-zeroʳ; *-zeroˡ; *-distribʳ-+; *-distribˡ-+; +-assoc; *-assoc)
open import AKS.Algebra.Divisibility *-+-semiring using (_∣_; divides; ∣-refl; ∣-trans; _∣0; 0∣n⇒n≈0; IsGCD; module GCD)

open import Polynomial.Simple.Reflection using (solve)
open import Polynomial.Simple.AlmostCommutativeRing.Instances using (module Nat)

gcdₕ : ∀ (a b : ℕ) → Acc _<_ b → ℕ
gcdₕ a zero (acc downward) = a
gcdₕ a (suc b) (acc downward) = gcdₕ (suc b) (a % suc b) (downward _ (n%m<m a (suc b)))

gcd : ℕ → ℕ → ℕ
gcd a b = gcdₕ a b <-well-founded

∣a∣b%a⇒∣b : ∀ {c a b} {a≢0 : False (a ≟ 0)} → c ∣ a → c ∣ (b % a) {a≢0} → c ∣ b
∣a∣b%a⇒∣b {c} {suc a} {b} (divides q₁ 1+a≡q₁*c) (divides q₂ b%a≡q₂*c) = divides (q₂ + b / suc a * q₁) $ begin
  b                               ≡⟨ m≡m%n+[m/n]*n b (suc a) ⟩
  b % suc a + (b / suc a) * suc a ≡⟨ cong (λ x → x + (b / suc a) * suc a) b%a≡q₂*c ⟩
  q₂ * c + (b / suc a) * suc a    ≡⟨ cong (λ x → q₂ * c + (b / suc a) * x) 1+a≡q₁*c ⟩
  q₂ * c + (b / suc a) * (q₁ * c) ≡⟨ lemma c q₂ (b / suc a) q₁ ⟩
  (q₂ + b / suc a * q₁) * c       ∎
  where
  lemma : ∀ c x y z → x * c + y * (z * c) ≡ (x + y * z) * c
  lemma = solve Nat.ring

gcd[a,b]∣a×gcd[a,b]∣b : ∀ a b → gcd a b ∣ a × gcd a b ∣ b
gcd[a,b]∣a×gcd[a,b]∣b a b = loop a b <-well-founded
  where
  loop : ∀ a b (rec : Acc _<_ b) → gcdₕ a b rec ∣ a × gcdₕ a b rec ∣ b
  loop a zero    (acc downward) = ∣-refl , a ∣0
  loop a (suc b) (acc downward) with loop (suc b) (a % suc b) (downward _ (n%m<m a (suc b)))
  ... | gcd∣b , gcd∣a%b = ∣a∣b%a⇒∣b gcd∣b gcd∣a%b , gcd∣b

∣a∣b⇒∣a%b : ∀ {c a b} {b≢0 : False (b ≟ 0)} → c ∣ a → c ∣ b → c ∣ (a % b) {b≢0}
∣a∣b⇒∣a%b {zero} {a} {suc b} c∣a c∣b with 0∣n⇒n≈0 c∣b
... | ()
∣a∣b⇒∣a%b {suc c} {a} {suc b} (divides q₁ refl) (divides (suc q₂) refl) = divides (q₁ % suc q₂) (*-dist-% c q₁ q₂)
  where
  open import AKS.Unsafe using (TODO)
  *-dist-% : ∀ c x y → (x * suc c) % (suc y * suc c) ≡ (x % suc y) * suc c
  *-dist-% = TODO

gcd-greatest : ∀ {c a b} → c ∣ a → c ∣ b → c ∣ gcd a b
gcd-greatest {c} {a} {b} c∣a c∣b = loop c a b <-well-founded c∣a c∣b
  where
  loop : ∀ c a b (rec : Acc _<_ b) → c ∣ a → c ∣ b → c ∣ gcdₕ a b rec
  loop c a zero    (acc downward) c∣a c∣b = c∣a
  loop c a (suc b) (acc downward) c∣a c∣b =
    loop c (suc b) (a % suc b) (downward _ (n%m<m a (suc b))) c∣b (∣a∣b⇒∣a%b c∣a c∣b)

gcd-isGCD : IsGCD gcd
gcd-isGCD = record
  { gcd[a,b]∣a = λ a b → proj₁ (gcd[a,b]∣a×gcd[a,b]∣b a b)
  ; gcd[a,b]∣b = λ a b → proj₂ (gcd[a,b]∣a×gcd[a,b]∣b a b)
  ; gcd-greatest = gcd-greatest
  }

∣-antisym : Antisymmetric _≡_ _∣_
∣-antisym {x} {y} (divides zero refl) (divides q₂ refl) = *-zeroʳ q₂
∣-antisym {x} {y} (divides (suc q₁) refl) (divides zero refl) = sym (*-zeroʳ (suc q₁))
∣-antisym {x} {y} (divides (suc q₁) pf₁) (divides (suc q₂) pf₂) = ≤-antisym (lte (q₁ * x) (sym pf₁)) (lte (q₂ * y) (sym pf₂))

open GCD gcd-isGCD ∣-antisym
  using
    ( Bézout; lemma; Identity; +ˡ; +ʳ; identity-base
    ; _⊥_; ⊥-sym; ⊥-respˡ; ⊥-respʳ
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

data Bézoutₕ (a : ℕ) (b : ℕ) (rec : Acc _<_ b) : Set where
  lemmaₕ : ∀ d → gcdₕ a b rec ≡ d → Identity d a b → Bézoutₕ a b rec

stepʳ
  : ∀ d x y a b {b≢0}
  → d + x * b ≡ y * (a % b) {b≢0}
  → d + (x + y * (a / b) {b≢0}) * b ≡ y * a
stepʳ d x y a b {b≢0} d+x*b≈y*[a%b] = begin
  d + (x + y * (a / b)) * b     ≡⟨ cong (λ t → d + t) (*-distribʳ-+ b x (y * (a / b))) ⟩
  d + (x * b + y * (a / b) * b) ≡⟨ sym (+-assoc d (x * b) (y * (a / b) * b)) ⟩
  (d + x * b) + y * (a / b) * b ≡⟨ cong (λ t → t + y * (a / b) {b≢0} * b) d+x*b≈y*[a%b] ⟩
  y * (a % b) + y * (a / b) * b ≡⟨ cong (λ t → y * (a % b) {b≢0} + t) (*-assoc y ((a / b) {b≢0}) b) ⟩
  y * (a % b) + y * (a / b * b) ≡⟨ sym (*-distribˡ-+ y (a % b) (a / b * b)) ⟩
  y * (a % b + a / b * b)       ≡⟨ cong (λ t → y * t) (sym (m≡m%n+[m/n]*n a b {b≢0})) ⟩
  y * a                         ∎

stepˡ
  : ∀ d x y a b {b≢0}
  → d + y * (a % b) {b≢0} ≡ x * b
  → d + y * a ≡ (x + y * (a / b) {b≢0}) * b
stepˡ d x y a b {b≢0} d+x*b≈y*[a%b] = begin
  d + y * a                           ≡⟨ cong (λ t → d + y * t) (m≡m%n+[m/n]*n a b {b≢0}) ⟩
  d + y * (a % b + a / b * b)         ≡⟨ cong (λ t → d + t) (*-distribˡ-+ y (a % b) (a / b * b)) ⟩
  d + (y * (a % b) + y * (a / b * b)) ≡⟨ sym (+-assoc d (y * (a % b)) (y * (a / b * b))) ⟩
  (d + y * (a % b)) + y * (a / b * b) ≡⟨ cong (λ t → t + y * ((a / b) {b≢0} * b)) d+x*b≈y*[a%b] ⟩
  x * b + y * (a / b * b)             ≡⟨ cong (λ t → x * b + t) (sym (*-assoc y (a / b) b)) ⟩
  x * b + y * (a / b) * b             ≡⟨ sym (*-distribʳ-+ b x (y * (a / b))) ⟩
  (x + y * (a / b)) * b               ∎

bézoutₕ : ∀ a b (rec : Acc _<_ b) → Bézoutₕ a b rec
bézoutₕ a zero    (acc downward) = lemmaₕ a refl identity-base
bézoutₕ a (suc b) (acc downward) with bézoutₕ (suc b) (a % suc b) (downward _ (n%m<m a (suc b)))
... | lemmaₕ d refl (+ʳ x y d+x*b≈y*[a%b]) = lemmaₕ d refl (+ˡ y (x + y * (a / suc b)) (stepʳ d x y a (suc b) d+x*b≈y*[a%b]))
... | lemmaₕ d refl (+ˡ x y d+y*[a%b]≡x*b) = lemmaₕ d refl (+ʳ y (x + y * (a / suc b)) (stepˡ d x y a (suc b) d+y*[a%b]≡x*b))

bézout : ∀ a b → Bézout a b
bézout a b with bézoutₕ a b <-well-founded
... | lemmaₕ d pf ident = lemma d pf ident
