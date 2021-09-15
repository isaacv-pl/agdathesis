open import Level hiding (zero; suc)
open import Function
--open import lib
open import Relation.Binary.HeterogeneousEquality
  renaming (sym to hsym; trans to htrans; cong to hcong; subst to hsubst)
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Algebra
open import Data.Nat.Properties
module ℕplus = CommutativeSemiring *-+-commutativeSemiring


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

{-
inc : ∀ {n} → Bin n → Bin (suc n)
inc zero = 2*n+1 zero
inc (2*n b) = 2*n+1 b
inc (2*n+1 {n} b) rewrite suc-lem n = 2*n (inc b)
-}

-- inc zero = Bin 1
-- inc (2*n (Bin 2)) = Bin 5
-- inc (2*n+1 (Bin 2)) = Bin 6

inc : ∀ {n} → Bin n → Bin (suc n)
inc zero = 2*n+1 zero
inc (2*n b) = 2*n+1 b
inc (2*n+1 {n} b) = subst (Bin ∘ suc) (ℕplus.+-comm n (suc n)) (2*n (inc b))

nat2bin : (n : ℕ) → Bin n
nat2bin zero = zero
nat2bin (suc n) = inc (nat2bin n)

bin2nat : ∀ {n} → Bin n → ℕ
bin2nat {n} b = n

--_$_ : {a b : Level} {A : Set a} {B : A → Set b} → ((x : A) → B x) → (x : A) → B x

--_≡_ : {a : Level} {A : Set a} → A → A → Set a
--_≅_ : {a : Level} {A : Set a} → A → {b : Level} {B : Set b} → B → Set a

--hsym : {A.a : Level} {A : Set A.a} {B.b : Level} {B : Set B.b} {x : A} {y : B} → x ≅ y → y ≅ x

-- ≡-subst-removable : ∀ {a p} {A : Set a}
--                    (P : A → Set p) {x y} (eq : x ≡ y) z →
--                    P.subst P eq z ≅ z

-- _∘_ : {a b c : Level} {A : Set a} {B : A → Set b}
-- {C : {x : A} → B x → Set c} →
-- ({x : A} (y : B x) → C y) → (g : (x : A) → B x) (x : A) → C (g x)

-- Bin ∘ suc : (x : ℕ) → Set (Dependent type of Bin)

-- ℕplus.+-comm (suc n) (suc (suc n)) : suc (n + suc (suc n)) ≡ suc (suc (n + suc n))
-- 2*n $ inc $ inc $ nat2bin n : Bin (suc (suc (n + suc (suc n))))
-- cong :
-- {A.a : Level} {A : Set A.a} {B.b : Level} {B : Set B.b} (f : A → B)
-- {x y : A} →
-- x ≡ y → f x ≡ f y

--hcong :
--{a b : Level} {A : Set a} {B : A → Set b} {x y : A}
--(f : (x₁ : A) → B x₁) →
--x ≅ y → f x ≅ f y

hcong' : {α β γ : Level} {I : Set α} {i j : I}
       -> (A : I -> Set β) {B : {k : I} -> A k -> Set γ} {x : A i} {y : A j}
       -> i ≡ j
       -> (f : {k : I} -> (x : A k) -> B x)
       -> x ≅ y
       -> f x ≅ f y
hcong' _ refl _ refl = refl

lem : ∀ n → 2*n+1 (inc (nat2bin n)) ≅ inc (inc (2*n+1 (nat2bin n)))
lem zero = refl
lem (suc n) = {!!}

{-
lem : ∀ n → 2*n+1 (inc (nat2bin n)) ≅ inc (inc (2*n+1 (nat2bin n)))
lem zero = refl
lem (suc n) = hcong' (Bin ∘ suc)
    (ℕplus.+-comm (suc n) (suc (suc n)))
    inc $ hsym $ ≡-subst-removable
          (Bin ∘ suc)
          (ℕplus.+-comm (suc n) (suc (suc n)))
          (2*n $ inc $ inc $ nat2bin n)
-}
