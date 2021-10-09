import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

infix 4 _<_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

infix 4 _>_

data _>_ : ℕ → ℕ → Set where
  s>z : ∀ {n : ℕ} → suc n > zero
  s>s : ∀ {m n : ℕ} → m > n → suc m > suc n

<>-flip : ∀ (m n : ℕ) → m < n → n > m
<>-flip zero (suc n) (z<s {n}) = s>z
<>-flip (suc m) (suc n) (s<s {m} {n} m<n) = s>s (<>-flip m n m<n)

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans {zero} {suc n} {suc p} (z<s {n}) n<p = z<s
<-trans {suc m} {suc n} {suc p} (s<s m<n) (s<s n<p) = s<s (<-trans {m} {n} {p} m<n n<p)

≤-iff-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤-iff-< zero (suc n) (s≤s m≤n) = z<s
≤-iff-< (suc m) (suc n) (s≤s m≤n) = s<s (≤-iff-< m n m≤n)

<-iff-≤ : ∀ (m n : ℕ) → m < suc n → m ≤ n
<-iff-≤ zero n m<n = z≤n
<-iff-≤ (suc m) (suc n) (s<s m<n) = s≤s (<-iff-≤ m n m<n)

data Trichotomy (m n : ℕ) : Set where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : m > n → Trichotomy m n

trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = eq refl
trichotomy zero (suc n) = lt z<s
trichotomy (suc m) zero = gt s>z
trichotomy (suc m) (suc n) = helper (trichotomy m n)
  where helper : Trichotomy m n → Trichotomy (suc m) (suc n)
        helper (lt m<n) = lt (s<s m<n)
        helper (eq m≡n) = eq (cong suc m≡n)
        helper (gt m>n) = gt (s>s m>n)        

+-monoᵣ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoᵣ-< zero p q p<q = p<q
+-monoᵣ-< (suc n) p q p<q = s<s (+-monoᵣ-< n p q p<q)

+-monoₗ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoₗ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoᵣ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoₗ-< m n p m<n) (+-monoᵣ-< n p q p<q)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

toBin : ℕ → Bin
toBin 0 = ⟨⟩
toBin (suc n) = inc (toBin n)

fromBin : Bin → ℕ
fromBin ⟨⟩ = 0
fromBin (x O) = (fromBin x) * 2
fromBin (x I) = ((fromBin x) * 2) + 1

data Can : Bin → Set where
  zero : Can ⟨⟩
  csuc : ∀ {b : Bin} → Can b → Can (inc b)

proof₁ : ∀ {n : ℕ} → Can (toBin n)
proof₁ {zero} = zero
proof₁ {suc n} = csuc {toBin n} (proof₁ {n})

lemma₁ : ∀ {n : ℕ} → n + 1 ≡ suc n
lemma₁ {zero} = refl
lemma₁ {suc n} = begin (suc n) + 1 ≡⟨⟩ suc (n + 1) ≡⟨ cong suc (lemma₁ {n}) ⟩ suc (suc n) ∎

lemma₂ : ∀ {b : Bin} → fromBin (inc b) ≡ suc (fromBin b)
lemma₂ {⟨⟩} = refl
lemma₂ {b O} = begin
  fromBin (inc (b O))
 ≡⟨⟩ fromBin b * 2 + 1
 ≡⟨ lemma₁ {fromBin b * 2} ⟩ suc (fromBin b * 2) ∎
lemma₂ {b I} = begin
  fromBin (inc (b I))
 ≡⟨⟩ fromBin (inc b) * 2
 ≡⟨ cong (λ x → x * 2) (lemma₂ {b})⟩ suc (suc (fromBin b * 2))
 ≡⟨ cong suc (sym (lemma₂ {b O}))⟩ suc (fromBin b * 2 + 1) ∎

lemma₃ : ∀ {n : ℕ} → inc (toBin n) ≡ toBin (suc n)
lemma₃ {n} = refl

proof₂ : ∀ {b : Bin} → Can b → toBin (fromBin b) ≡ b
proof₂ {_} zero = refl
proof₂ {b = .(inc ⟨⟩)} (csuc {⟨⟩} can-b₁) = refl
proof₂ {b = .(inc (b₁ O))} (csuc {b₁ O} can-b₁) = begin
  toBin (fromBin (inc (b₁ O)))
 ≡⟨⟩ toBin (fromBin b₁ * 2 + 1)
 ≡⟨ cong toBin (lemma₁ {(fromBin b₁) * 2}) ⟩ toBin (suc (fromBin b₁ * 2))
 ≡⟨⟩ inc (toBin (fromBin b₁ * 2))
 ≡⟨ cong inc (proof₂ {b₁ O} can-b₁)⟩ (b₁ I)
 ≡⟨⟩ (b₁ I) ∎
proof₂ {b = .(inc (b₁ I))} (csuc {b₁ I} can-b₁) = begin
  toBin (fromBin (inc (b₁ I)))
 ≡⟨⟩ toBin (fromBin ((inc b₁) O))
 ≡⟨⟩ toBin ((fromBin (inc b₁)) * 2)
 ≡⟨ cong (λ x → toBin (x * 2)) (lemma₂ {b₁}) ⟩ inc (inc (toBin (fromBin b₁ * 2)))
 ≡⟨⟩ inc (toBin (suc (fromBin b₁ * 2)))
 ≡⟨ cong (λ x → inc (toBin x)) (sym (lemma₂ {b₁ O})) ⟩ inc (toBin (fromBin (b₁ I)))
 ≡⟨ cong inc (proof₂ {b₁ I} can-b₁) ⟩ (inc b₁ O) ∎

