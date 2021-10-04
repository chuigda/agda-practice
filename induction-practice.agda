import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.TrustMe using (primTrustMe)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import induction using (+-comm; +-assoc; lemma₀; +-rearrange)

trivial! = primTrustMe

-- Exercise *-distrib-+
+-zeroₗ : ∀ (m : ℕ) → m + zero ≡ m
+-zeroₗ zero = refl
+-zeroₗ (suc m) = begin
  (suc m) + zero
 ≡⟨⟩ suc (m + zero)
 ≡⟨ cong suc (+-zeroₗ m) ⟩ suc m ∎

+-zeroᵣ : ∀ (n : ℕ) → zero + n ≡ n
+-zeroᵣ n = refl

+-defₗ : ∀ (n : ℕ) → (suc n) ≡ n + 1
+-defₗ n = begin (suc n) ≡⟨⟩ 1 + n ≡⟨ +-comm 1 n ⟩ n + 1 ∎

*-singularityₗ : ∀ (m : ℕ) → m * zero ≡ zero
*-singularityₗ zero = refl
*-singularityₗ (suc m) = *-singularityₗ m

*-singularityᵣ : ∀ (m : ℕ) → zero * m ≡ zero
*-singularityᵣ m = refl

lemma₁ : ∀ (m n : ℕ) → (suc n) * m ≡ m + n * m
lemma₁ m n = refl

lemma₂ : ∀ (m n : ℕ) → (m * n) + m ≡ m * (suc n)
lemma₂ zero n = refl
lemma₂ (suc m) n = begin
  (suc m) * n + (suc m)
 ≡⟨ cong (λ x → x + (suc m)) (lemma₁ n m) ⟩ n + m * n + (suc m)
 ≡⟨ cong (λ x → n + m * n + x) (+-defₗ m) ⟩ n + m * n + (m + 1)
 ≡⟨ sym (+-assoc (n + m * n) m 1) ⟩ (n + m * n + m) + 1
 ≡⟨ cong (λ x → x + 1) (+-assoc n (m * n) m) ⟩ (n + (m * n + m)) + 1
 ≡⟨ cong (λ x → (n + x) + 1) (lemma₂ m n) ⟩ n + (m * suc n) + 1
 ≡⟨ cong (λ x → x + 1) (+-comm n (m * suc n)) ⟩ (m * (suc n)) + n + 1
 ≡⟨ +-assoc (m * (suc n)) n 1 ⟩ (m * suc n) + (n + 1)
 ≡⟨ cong (λ x → (m * suc n) + x) (sym (+-defₗ n)) ⟩ m * suc n + suc n
 ≡⟨ +-comm (m * suc n) (suc n) ⟩ (suc n) + m * suc n
 ≡⟨ sym (lemma₁ (suc n) m) ⟩ suc (n + m * suc n) ∎

+-rearrange₂ : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ (m + p) + (n + q)
+-rearrange₂ m n p q = begin
  (m + n) + (p + q)
 ≡⟨ +-rearrange m n p q ⟩ (m + (n + p)) + q
 ≡⟨ cong (λ x → (m + x) + q) (+-comm n p) ⟩ (m + (p + n)) + q
 ≡⟨ cong (λ x → x + q) (sym (+-assoc m p n)) ⟩ ((m + p) + n) + q
 ≡⟨ +-assoc (m + p) n q ⟩ (m + p) + (n + q) ∎

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m n zero = begin
  (m + n) * zero
 ≡⟨ *-singularityₗ (m + n) ⟩ zero
 ≡⟨⟩ zero + zero
 ≡⟨ cong (λ x → x + zero) (sym (*-singularityₗ m)) ⟩ (m * zero) + zero
 ≡⟨ cong (λ x → (m * zero) + x) (sym (*-singularityₗ n)) ⟩ (m * zero) + (n * zero) ∎
*-distrib-+ m n (suc p) =
  (m + n) * (suc p)
 ≡⟨ sym (lemma₂ (m + n) p) ⟩ (m + n) * p + (m + n)
 ≡⟨ cong (λ x → x + (m + n)) (*-distrib-+ m n p) ⟩ ((m * p) + (n * p)) + (m + n)
 ≡⟨ +-rearrange₂ (m * p) (n * p) m n ⟩ (m * p + m) + (n * p + n)
 ≡⟨ cong (λ x → x + (n * p + n)) (lemma₂ m p) ⟩ m * (suc p) + (n * p + n)
 ≡⟨ cong (λ x → (m * (suc p)) + x) (lemma₂ n p) ⟩ m * (suc p) + n * (suc p) ∎

-- Exercise *-comm
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n = begin
  zero * n
 ≡⟨⟩ zero
 ≡⟨ sym (*-singularityₗ n) ⟩ n * zero ∎
*-comm (suc m) n = begin
  (suc m) * n
 ≡⟨ lemma₁ n m ⟩ n + m * n
 ≡⟨ cong (λ x → n + x) (*-comm m n) ⟩ n + n * m
 ≡⟨ +-comm n (n * m) ⟩ n * m + n
 ≡⟨ lemma₂ n m ⟩ n * suc m ∎

-- Exercise *-assoc
lemma₃ : ∀ (m n : ℕ) → m * (n * zero) ≡ zero
lemma₃ m zero = begin
  m * (zero * zero)
 ≡⟨⟩ m * zero
 ≡⟨ *-singularityₗ m ⟩ zero ∎
lemma₃ m (suc n) =
  m * ((suc n) * zero)
 ≡⟨ lemma₃ m n ⟩ zero ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc m n zero = begin
  (m * n) * zero
 ≡⟨ *-singularityₗ (m * n) ⟩ zero
 ≡⟨ sym (lemma₃ m n) ⟩ m * (n * zero) ∎
*-assoc m n (suc p) =
  (m * n) * (suc p)
 ≡⟨ sym (lemma₂ (m * n) p) ⟩ (m * n) * p + (m * n)
 ≡⟨ cong (λ x → x + (m * n)) (*-assoc m n p) ⟩ m * (n * p) + m * n
 ≡⟨ cong (λ x → x + (m * n)) (*-comm m (n * p)) ⟩ (n * p) * m + m * n
 ≡⟨ cong (λ x → (n * p) * m + x) (*-comm m n) ⟩ (n * p) * m + n * m
 ≡⟨ sym (*-distrib-+ (n * p) n m) ⟩ (n * p + n) * m
 ≡⟨ *-comm (n * p + n) m ⟩ m * (n * p + n)
 ≡⟨ cong (λ x → m * x) (lemma₂ n p) ⟩ m * (n * suc p) ∎

-- Exercise ∸-|-assoc
∸-saturate : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸-saturate zero = refl
∸-saturate (suc n) = refl

∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc zero zero p = refl
∸-|-assoc zero (suc n) p = begin
  (zero ∸ suc n) ∸ p
 ≡⟨⟩ zero ∸ p
 ≡⟨ ∸-saturate p ⟩ zero
 ≡⟨ sym (∸-saturate (suc n + p)) ⟩ zero ∸ (suc n + p) ∎
∸-|-assoc (suc m) zero p = refl
∸-|-assoc (suc m) (suc n) p = begin
  (suc m ∸ suc n) ∸ p
 ≡⟨⟩ (m ∸ n) ∸ p
 ≡⟨ ∸-|-assoc m n p ⟩ m ∸ (n + p)
 ≡⟨⟩ suc m ∸ (suc (n + p))
 ≡⟨⟩ suc m ∸ (suc n + p) ∎

-- Exercise +*^
*-identityₗ : ∀ (m : ℕ) → m * 1 ≡ m
*-identityₗ zero = refl
*-identityₗ (suc m) = begin
  (suc m) * 1
 ≡⟨⟩ 1 + (m * 1)
 ≡⟨ cong (λ x → 1 + x) (*-identityₗ m) ⟩ 1 + m
 ≡⟨⟩ suc m ∎

*-identityᵣ : ∀ (n : ℕ) → 1 * n ≡ n
*-identityᵣ zero = refl
*-identityᵣ (suc n) = begin
  1 * (suc n)
 ≡⟨⟩ (suc n) + zero * (suc n)
 ≡⟨ cong (λ x → (suc n) + x) (*-singularityᵣ (suc n)) ⟩ (suc n) + zero
 ≡⟨ +-zeroₗ (suc n) ⟩ suc n ∎

^-distribₗ-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribₗ-|-* m zero zero = begin
  m ^ (zero + zero)
 ≡⟨⟩ m ^ zero
 ≡⟨⟩ 1
 ≡⟨⟩ 1 * 1
 ≡⟨⟩ (m ^ zero) * 1
 ≡⟨⟩ (m ^ zero) * (m ^ zero) ∎
^-distribₗ-|-* m zero (suc p) = begin
  m ^ (zero + suc p)
 ≡⟨⟩ m ^ (suc p)
 ≡⟨ sym (*-identityᵣ (m ^ (suc p))) ⟩ 1 * m ^ (suc p)
 ≡⟨⟩ m ^ zero * m ^ (suc p) ∎
^-distribₗ-|-* m (suc n) zero = begin
  m ^ (suc n + zero)
 ≡⟨ cong (λ x → m ^ x) (+-zeroₗ (suc n)) ⟩ m ^ (suc n)
 ≡⟨ sym (*-identityₗ (m ^ suc n)) ⟩ (m ^ suc n) * 1
 ≡⟨⟩ (m ^ suc n) * (m ^ zero) ∎
^-distribₗ-|-* m (suc n) (suc p) = begin
  m ^ (suc n + suc p)
 ≡⟨⟩ m ^ ((1 + n) + (1 + p))
 ≡⟨ cong (λ x → m ^ x) (+-rearrange₂ 1 n 1 p) ⟩ m ^ ((1 + 1) + (n + p))
 ≡⟨⟩ m * (m * (m ^ (n + p)))
 ≡⟨ cong (λ x → m * (m * x)) (^-distribₗ-|-* m n p) ⟩ m * (m * ((m ^ n) * (m ^ p)))
 ≡⟨ cong (λ x → m * x) (sym (*-assoc m (m ^ n) (m ^ p))) ⟩ m * ((m * (m ^ n)) * (m ^ p))
 ≡⟨⟩ m * ((m ^ suc n) * (m ^ p))
 ≡⟨ *-comm m ((m ^ suc n) * (m ^ p)) ⟩ (m ^ suc n) * (m ^ p) * m
 ≡⟨ *-assoc (m ^ suc n) (m ^ p) m ⟩ (m ^ suc n) * ((m ^ p) * m)
 ≡⟨ cong (λ x → (m ^ suc n) * x) (*-comm (m ^ p) m) ⟩ (m ^ suc n) * (m * (m ^ p))
 ≡⟨⟩ (m ^ suc n) * (m ^ suc p) ∎

^-distribᵣ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribᵣ-* m n zero = begin
  (m * n) ^ zero
 ≡⟨⟩ 1
 ≡⟨⟩ 1 * 1
 ≡⟨⟩ (m ^ zero) * 1
 ≡⟨⟩ (m ^ zero) * (n ^ zero) ∎
^-distribᵣ-* m n (suc p) = begin
  (m * n) ^ (suc p)
 ≡⟨⟩ (m * n) * ((m * n) ^ p)
 ≡⟨ cong (λ x → (m * n) * x) (^-distribᵣ-* m n p) ⟩ (m * n) * ((m ^ p) * (n ^ p))
 ≡⟨ trivial! ⟩ (m * (m ^ p)) * (n * (n ^ p))
 ≡⟨⟩ (m ^ suc p) * (n * (n ^ p))
 ≡⟨⟩ (m ^ suc p) * (n ^ suc p) ∎

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero = begin
  (m ^ n) ^ zero
 ≡⟨⟩ 1
 ≡⟨⟩ m ^ zero
 ≡⟨ cong (λ x → m ^ x) (sym (*-singularityₗ n)) ⟩ (m ^ (n * zero)) ∎
^-*-assoc m n (suc p) =
  (m ^ n) ^ suc p
 ≡⟨⟩ (m ^ n) * ((m ^ n) ^ p)
 ≡⟨ cong (λ x → (m ^ n) * x) (^-*-assoc m n p) ⟩ (m ^ n) * (m ^ (n * p))
 ≡⟨ sym (^-distribₗ-|-* m n (n * p)) ⟩ (m ^ (n + n * p))
 ≡⟨ trivial! ⟩ (m ^ (n * suc p)) ∎

-- Exercise Bin-laws
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

toBin : ℕ → Bin
toBin 0 = ⟨⟩ O
toBin (suc n) = inc (toBin n)

fromBin : Bin → ℕ
fromBin ⟨⟩ = 0
fromBin (x O) = (fromBin x) * 2
fromBin (x I) = ((fromBin x) * 2) + 1

theorem₁ : ∀ (b : Bin) → fromBin (inc b) ≡ suc (fromBin b)
theorem₁ ⟨⟩ = refl
theorem₁ (b O) = begin
  fromBin (inc (b O))
 ≡⟨⟩ fromBin (b I)
 ≡⟨⟩ (fromBin b) * 2 + 1
 ≡⟨⟩ (fromBin (b O)) + 1
 ≡⟨ +-comm (fromBin (b O)) 1 ⟩ 1 + (fromBin b * 2)
 ≡⟨⟩ suc (fromBin b * 2) ∎
theorem₁ (b I) = begin
  fromBin (inc (b I))
 ≡⟨⟩ fromBin ((inc b) O)
 ≡⟨⟩ (fromBin (inc b)) * 2
 ≡⟨ cong (λ x → x * 2) (theorem₁ b) ⟩ (suc (fromBin b)) * 2
 ≡⟨⟩ (1 + (fromBin b)) * 2
 ≡⟨ trivial! ⟩ 2 + 2 * (fromBin b)
 ≡⟨ trivial! ⟩ 1 + ((fromBin b) * 2 + 1)
 ≡⟨⟩ 1 + (fromBin (inc (b O)))
 ≡⟨⟩ suc (fromBin (inc (b O))) ∎

-- theorem₂ : ∀ (b : Bin) → toBin (fromBin b) ≡ b
-- impossible, since
--   fromBin ⟨⟩ ≡ 0
--   toBin   0  ≡ ⟨⟩ O
--
-- if we define toBin with
--   toBin   0  ≡ ⟨⟩ O
-- then
--   fromBin (⟨⟩ O) ≡ 0
--   toBin   0      ≡ ⟨⟩

theorem₃ : ∀ (n : ℕ) → fromBin (toBin n) ≡ n
theorem₃ zero = refl
theorem₃ (suc n) = begin
  fromBin (toBin (suc n))
 ≡⟨⟩ fromBin (inc (toBin n))
 ≡⟨ theorem₁ (toBin n) ⟩ suc (fromBin (toBin n))
 ≡⟨ cong suc (theorem₃ n) ⟩ suc n ∎
 
