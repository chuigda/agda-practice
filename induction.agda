module induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.TrustMe using (primTrustMe)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

trivial! = primTrustMe

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = begin
  (suc m) + n + p
 ≡⟨⟩ suc (m + n) + p
 ≡⟨⟩ suc ((m + n) + p)
 ≡⟨ cong suc (+-assoc m n p) ⟩ suc (m + (n + p))
 ∎

+-identityₗ : ∀ (n : ℕ) → zero + n ≡ n
+-identityₗ n = refl

+-identityᵣ : ∀ (n : ℕ) → n + zero ≡ n
+-identityᵣ zero = refl
+-identityᵣ (suc n) = begin
  (suc n) + zero
 ≡⟨⟩ suc (n + zero)
 ≡⟨ cong suc (+-identityᵣ n) ⟩ suc n
 ∎

lemma₀ : ∀ (m n : ℕ) → m + (suc n) ≡ suc (m + n)
lemma₀ zero n = refl
lemma₀ (suc m) n = begin
  (suc m) + (suc n)
 ≡⟨⟩ suc (m + (suc n))
 ≡⟨ cong suc (lemma₀ m n) ⟩ suc (suc (m + n))
 ≡⟨⟩ suc (suc (m + n))
 ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n = begin
  zero + n
 ≡⟨ +-identityₗ n ⟩ n
 ≡⟨ sym (+-identityᵣ n) ⟩ n + zero
 ∎
+-comm (suc m) n = begin
  (suc m) + n
 ≡⟨⟩ suc (m + n)
 ≡⟨ cong suc (+-comm m n) ⟩ suc (n + m)
 ≡⟨ sym (lemma₀ n m) ⟩ n + (suc m)
 ∎

-- 自己写的
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange zero n p q = begin
  (zero + n) + (p + q)
 ≡⟨⟩ n + (p + q)
 ≡⟨ sym (+-assoc n p q) ⟩ (n + p) + q
 ≡⟨⟩ 0 + (n + p) + q ∎
+-rearrange (suc m) n p q =
  ((suc m) + n) + (p + q)
 ≡⟨⟩ (suc (m + n)) + (p + q)
 ≡⟨⟩ suc ((m + n) + (p + q))
 ≡⟨ cong suc (+-rearrange m n p q) ⟩ suc (m + (n + p) + q) ∎

+-rearrange₁ : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange₁ m n p q = begin
  (m + n) + (p + q)
 ≡⟨ +-assoc m n (p + q) ⟩ m + (n + (p + q))
 ≡⟨ cong (_+_ m) (sym (+-assoc n p q)) ⟩ m + ((n + p) + q)
 ≡⟨ sym (+-assoc m (n + p) q) ⟩ m + (n + p) + q ∎

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p = begin
  m + (n + p)
 ≡⟨ sym (+-assoc m n p) ⟩ (m + n) + p
 ≡⟨ cong (λ x → x + p) (+-comm m n) ⟩ (n + m) + p
 ≡⟨ +-assoc n m p ⟩ n + (m + p) ∎
