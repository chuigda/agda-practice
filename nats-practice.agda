open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import nats using (ℕ; zero; suc; _+_; _*_; _∸_)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

toBin : ℕ → Bin
toBin 0 = ⟨⟩ O
toBin (suc n) = inc (toBin n)

_ : toBin 11 ≡ ⟨⟩ I O I I
_ = refl

fromBin : Bin → ℕ
fromBin ⟨⟩ = 0
fromBin (x O) = (fromBin x) * 2
fromBin (x I) = ((fromBin x) * 2) + 1

_ : fromBin (⟨⟩ I O I I) ≡ 11
_ = refl
