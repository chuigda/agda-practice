module relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

data _≤_ : ℕ → ℕ → Set where
  -- base case: 0 ≤ 任何数
  z≤n : ∀ {n : ℕ} → zero ≤ n
  -- inductive case: 若 m ≤ n，则有 (m + 1) ≤ (n + 1)
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s {m} {n} m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n {zero}
≤-refl {suc n} = s≤s {n} {n} (≤-refl {n})

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans {zero} {n} {p} (z≤n {n}) _ = z≤n {p}
≤-trans {suc m} {suc n} {suc p} (s≤s {m} {n} m≤n) (s≤s {n} {p} n≤p) = s≤s {m} {p} (≤-trans {m} {n} {p} m≤n n≤p)

≤-trans' : ∀ (m n p : ℕ) → m ≤ n → n ≤ p → m ≤ p
≤-trans' zero n p z≤n _ = z≤n
≤-trans' (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans' m n p m≤n n≤p)

≤-antisym' : ∀ (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
≤-antisym' zero zero m≤n n≤m = refl
≤-antisym' (suc m) (suc n) (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym' m n m≤n n≤m)

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n)
  -- 简化写法
  with ≤-total m n
...    | forward m≤n = forward (s≤s m≤n)
...    | flipped n≤m = flipped (s≤s n≤m)

≤-total' : ∀ (m n : ℕ) → Total m n
≤-total' zero n = forward z≤n
≤-total' (suc m) zero = flipped z≤n
≤-total' (suc m) (suc n) = helper (≤-total' m n)
        -- 已知 m 和 n 符合全序关系，使用 helper 获得 suc m 和 suc n 也构成全序关系
  where helper : Total m n → Total (suc m) (suc n)
        helper (forward m≤n) = forward (s≤s m≤n)
        helper (flipped m≤n) = flipped (s≤s m≤n)

+-monoᵣ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoᵣ-≤ zero p q p≤q = p≤q
+-monoᵣ-≤ (suc n) p q p≤q = s≤s (+-monoᵣ-≤ n p q p≤q)

+-monoₗ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoₗ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoᵣ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoₗ-≤ m n p m≤n) (+-monoᵣ-≤ n p q p≤q)

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)
e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd (m + n)

e+e≡e zero n = n
e+e≡e (suc om) en = suc (o+e≡o om en)
o+e≡o (suc em) en = suc (e+e≡e em en)
e+o≡o {m} {n} em en rewrite +-comm m n = o+e≡o en em

postulate
  lemma₀ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e {m} {suc n} om (suc en) rewrite lemma₀ m n = suc (o+e≡o om en)

o+o≡e' : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e' {suc m} {n} (suc om) en = suc (e+o≡o om en)
