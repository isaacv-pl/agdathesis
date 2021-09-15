open import Level hiding (zero; suc)
open import Function
open import Relation.Binary.HeterogeneousEquality
  renaming (sym to hsym; trans to htrans; cong to hcong; subst to hsubst)
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Algebra
open import Data.Nat.Properties
module ℕplus = CommutativeSemiring commutativeSemiring


data Bin : ℕ → Set where
  zero  : Bin zero
  2*n   : ∀ {n} → Bin n → Bin (n + n)
  2*n+1 : ∀ {n} → Bin n → Bin (suc (n + n))

suc-lem : ∀ n → suc (suc (n + n)) ≡ suc n + suc n
suc-lem zero = refl
suc-lem (suc n) rewrite
    ℕplus.+-comm n (suc n)
  | suc-lem n | ℕplus.+-comm n (suc (suc n))
  | ℕplus.+-comm n (suc n) = refl

inc : ∀ {n} → Bin n → Bin (suc n)
inc zero = 2*n+1 zero
inc (2*n b) = 2*n+1 b
inc (2*n+1 {n} b) = subst (Bin ∘ suc) (ℕplus.+-comm n (suc n)) (2*n (inc b))

nat2bin : (n : ℕ) → Bin n
nat2bin zero = zero
nat2bin (suc n) = inc (nat2bin n)

bin2nat : ∀ {n} → Bin n → ℕ
bin2nat {n} b = n
