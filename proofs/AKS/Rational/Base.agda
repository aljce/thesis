open import Function.Equivalence as FE using ()
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Decidable using (False; map)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)
open ≡-Reasoning

open import Data.Product using (_×_; _,_; uncurry)

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.FromNat using (Number)

module AKS.Rational.Base where

open import Data.Integer using (ℤ; +_; +0; +[1+_]; -[1+_]; ∣_∣) renaming (_+_ to _+ℤ_; _*_ to _*ℤ_; -_ to -ℤ_; _≟_ to _≟ℤ_)
open import Data.Integer.DivMod using () renaming (_divℕ_ to _/ℤ_)
open import Data.Integer.Properties using (∣-n∣≡∣n∣)
open import AKS.Nat using (ℕ; suc; ≢⇒¬≟; ¬≟⇒≢) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≟_ to _≟ℕ_)
open import AKS.Nat using (n≢0∧m≢0⇒n*m≢0)
open import AKS.Nat.Divisibility using () renaming (_/_ to _/ℕ_)
open import AKS.Nat.GCD using (gcd; _⊥_; gcd[a,1]≡1; b≢0⇒gcd[a,b]≢0; gcd[0,a]≡1⇒a≡1; ⊥-respˡ; ⊥-sym)

record ℚ : Set where
  constructor ℚ✓
  field
    numerator : ℤ
    denominator : ℕ
    den≢0 : False (denominator ≟ℕ 0)
    coprime : ∣ numerator ∣ ⊥ denominator

fromℤ : ℤ → ℚ
fromℤ n = record
  { numerator = n
  ; denominator = 1
  ; den≢0 = tt
  ; coprime = gcd[a,1]≡1 (∣ n ∣)
  }

fromℕ : ℕ → ℚ
fromℕ n = fromℤ (+ n)

instance
  ℚ-number : Number ℚ
  ℚ-number = record
    { Constraint = λ _ → ⊤
    ; fromNat = λ n → fromℕ n
    }


open import AKS.Unsafe using (trustMe; TODO)

open import Data.Fin using (Fin)
open import Data.Nat.DivMod using (_divMod_; result)

∣a/ℤb∣≡∣a∣/ℕb : ∀ a b {b≢0} → ∣ (a /ℤ b) {b≢0} ∣ ≡ (∣ a ∣ /ℕ b) {b≢0}
∣a/ℤb∣≡∣a∣/ℕb (+ n) b {b≢0} = refl
∣a/ℤb∣≡∣a∣/ℕb (-[1+ x ]) b {b≢0} with (suc x divMod b) {b≢0}
... | result q Fin.zero eq rewrite ∣-n∣≡∣n∣ (+ q) = trustMe
... | result q (Fin.suc r) eq = trustMe

a/d⊥b/d : ∀ a b d {d≢0} → gcd a b ≡ d → (a /ℕ d) {d≢0} ⊥ (b /ℕ d) {d≢0}
a/d⊥b/d a b d gcd[a,b]≡d = begin
  gcd (a /ℕ d) (b /ℕ d) ≡⟨ trustMe ⟩
  1 ∎

a≢0⇒a/b≢0 : ∀ a b (a≢0 : False (a ≟ℕ 0)) {b≢0} → (a /ℕ b) {b≢0} ≢ 0
a≢0⇒a/b≢0 (suc a) (suc b) a≢0 = TODO

canonical : ∀ (num : ℤ) (den : ℕ) {den≢0 : False (den ≟ℕ 0)} → ℚ
canonical num den {den≢0} = construct num den {den≢0} (gcd ∣ num ∣ den) {≢⇒¬≟ (b≢0⇒gcd[a,b]≢0 (∣ num ∣) den (¬≟⇒≢ den≢0))} refl
  where
  construct : ∀ num den {den≢0 : False (den ≟ℕ 0)} d {d≢0 : False (d ≟ℕ 0)} → gcd ∣ num ∣ den ≡ d → ℚ
  construct num den {den≢0} d {d≢0} gcd[num,den]≡d = record
    { numerator = (num /ℤ d) {d≢0}
    ; denominator = (den /ℕ d) {d≢0}
    ; den≢0 = ≢⇒¬≟ (a≢0⇒a/b≢0 den d den≢0)
    ; coprime = ⊥-respˡ {den /ℕ d} (sym (∣a/ℤb∣≡∣a∣/ℕb num d)) (a/d⊥b/d ∣ num ∣ den d gcd[num,den]≡d)
    }

infixl 6 _+_
_+_ : ℚ → ℚ → ℚ
(ℚ✓ num₁ den₁ den₁≢0 _) + (ℚ✓ num₂ den₂ den₂≢0 _) = canonical (num₁ *ℤ (+ den₂) +ℤ num₂ *ℤ (+ den₁)) (den₁ *ℕ den₂) {≢⇒¬≟ (n≢0∧m≢0⇒n*m≢0 (¬≟⇒≢ den₁≢0) (¬≟⇒≢ den₂≢0))}

infix  8 -_
-_ : ℚ → ℚ
- (ℚ✓ num den den≢0 num⊥den) = ℚ✓ (-ℤ num) den den≢0 (⊥-respˡ {den} (sym (∣-n∣≡∣n∣ num)) num⊥den)

infixl 7 _*_
_*_ : ℚ → ℚ → ℚ
(ℚ✓ num₁ den₁ den₁≢0 _) * (ℚ✓ num₂ den₂ den₂≢0 _) = canonical (num₁ *ℤ num₂) (den₁ *ℕ den₂) {≢⇒¬≟ (n≢0∧m≢0⇒n*m≢0 (¬≟⇒≢ den₁≢0) (¬≟⇒≢ den₂≢0))}

infix 8 _⁻¹
_⁻¹ : ∀ (q : ℚ) {q≢0 : q ≢ 0} → ℚ
(ℚ✓ +0 den den≢0 num⊥den ⁻¹) {q≢0} with gcd[0,a]≡1⇒a≡1 den num⊥den
(ℚ✓ +0 .1 tt refl ⁻¹) {q≢0} | refl = contradiction refl q≢0
(ℚ✓ +[1+ num ] (suc den) den≢0 num⊥den) ⁻¹ = ℚ✓ +[1+ den ] (suc num) tt (⊥-sym {suc num} {suc den} num⊥den)
(ℚ✓ -[1+ num ] (suc den) den≢0 num⊥den) ⁻¹ = ℚ✓ -[1+ den ] (suc num) tt (⊥-sym {suc num} {suc den} num⊥den)

infixl 7 _/_
_/_ : ∀ (p q : ℚ) {q≢0 : q ≢ 0} → ℚ
_/_ p q {q≢0}= p * (q ⁻¹) {q≢0}

_≟_ : Decidable {A = ℚ} _≡_
(ℚ✓ num₁ (suc den₁) tt num₁⊥den₁) ≟ (ℚ✓ num₂ (suc den₂) tt num₂⊥den₂)
  = map (FE.equivalence forward backward) (num₁ ≟ℤ num₂ ×-dec den₁ ≟ℕ den₂)
  where
  forward : ∀ {num₁ num₂} {den₁ den₂} {num₁⊥den₁ num₂⊥den₂} → num₁ ≡ num₂ × den₁ ≡ den₂ → ℚ✓ num₁ (suc den₁) tt num₁⊥den₁ ≡ ℚ✓ num₂ (suc den₂) tt num₂⊥den₂
  forward {num₁} {num₂} {den₁} {den₂} {num₁⊥den₁} {num₂⊥den₂} (refl , refl) = cong (λ pf → ℚ✓ num₁ (suc den₁) tt pf) (≡-irrelevant num₁⊥den₁ num₂⊥den₂)
  backward : ∀ {num₁ num₂} {den₁ den₂} {num₁⊥den₁ num₂⊥den₂} → ℚ✓ num₁ (suc den₁) tt num₁⊥den₁ ≡ ℚ✓ num₂ (suc den₂) tt num₂⊥den₂ → num₁ ≡ num₂ × den₁ ≡ den₂
  backward refl = (refl , refl)

≢0 : ∀ {p : ℚ} {p≢0 : False (p ≟ 0)} → p ≢ 0
≢0 {p} with p ≟ 0
≢0 {p} | no p≢0 = p≢0

test = ((1 / 2) {≢0} + (3 / 4) {≢0}) ⁻¹

open import Data.String using (String; _++_)
open import Data.Nat.Show using () renaming (show to show-ℕ)

show-ℤ : ℤ → String
show-ℤ (+ n) = show-ℕ n
show-ℤ (-[1+ n ]) = "-" ++ show-ℕ (suc n)

show-ℚ : ℚ → String
show-ℚ (ℚ✓ num 1 _ _) = show-ℤ num
show-ℚ (ℚ✓ num den _ _) = show-ℤ num ++ "/" ++ show-ℕ den
