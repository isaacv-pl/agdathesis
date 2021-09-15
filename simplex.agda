{-# OPTIONS --rewriting #-}
module simplex  where
open import lib
open import Agda.Primitive public using (lzero; Level; _⊔_)



-- borrowed from Nat.agda worked with Matt
data _≡_ {A : Set} (a : A) : A → Set where
    refl : a ≡ a

--data _==_ {l : Level} {A : Set l} (M : A) : A → Set l where
--    id : M == M
-- Same definition of ∅ in src folder
data ∅ : Set where

∅-elim :
  {ℓ : Level}
  {A : Set ℓ}
  → ---------
  ∅ → A
∅-elim ()


postulate
  -- simplicial interval; 1-simplex
  Δ₁ : Set
  O  : Δ₁ --face maps from zero simplex
  I  : Δ₁ --face maps from zero

  _∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)

  -- can define connections from totality
  _⊓_ : Δ₁ → Δ₁ → Δ₁
  0⊓ : (x : Δ₁) → (O ⊓ x) == O
  ⊓0 : (x : Δ₁) → (x ⊓ O) == O
  1⊓ : (x : Δ₁) → (I ⊓ x) == x
  ⊓1 : (x : Δ₁) → (x ⊓ I) == x
  {-# REWRITE 0⊓ #-}
  {-# REWRITE ⊓0 #-}
  {-# REWRITE 1⊓ #-}
  {-# REWRITE ⊓1 #-}
  ⊓comm : (x y : Δ₁) → (x ⊓ y) == (y ⊓ x)
  ⊓idem : (x : Δ₁) → (x ⊓ x) == x
  ⊓assoc' : (x y : Δ₁) → ((x ⊓ y) ⊓ x) == (x ⊓ y) -- associative too, but haven't needed it yet
  {-# REWRITE ⊓idem #-}
  {-# REWRITE ⊓assoc' #-}

  -- showing that interval creates contradiction
  -- also taken from src folder
  ax2 : O ≡ I → ∅

  -- Triangle type which takes in three Nats and makes sure that they are partially ordered;
  -- Technically should be totally ordered, but we keep it partially ordered in the event of
  -- face maps and degeneracy maps. In a degeneracy map for example we could get
  -- [0, 1 ,2] → [0, 1, 1] where both 2 and 1 are mapped to 1. Therefore, we get to preserve
  -- structure, before applying axiom3 which shows that Δ₂ and Δ₁ are both equivalent.

  Δ₂ :  Set
  OI : Δ₁ → Δ₂ -- Face Maps for Δ₁ where OI delineates the line in the triangle hit by the 1-simplex
  I2 : Δ₁ → Δ₂
  O2 : Δ₁ → Δ₂
  --axioms for Face maps of Δ₁
  Δ₁FI : OI I ≡ I2 O -- connecting endpoints of paths
  Δ₁FO : OI O ≡ O2 O
  Δ₁F2 : O2 I ≡ I2 I

  --Degeneracy maps for Δ₂, where OI2 → OOI or OI2 → OII
  OOI : Δ₂ → Δ₁
  OII : Δ₂ → Δ₁
  --Axioms for Degen. maps of Δ₂
  Δ₂D0 : (OOI ∘ OI) ≡ λ x → O
  Δ₂D1 : (OOI ∘ O2) ≡ λ x → x
  Δ₂D2 : (OOI ∘ I2) ≡ λ x → x
  Δ₂D3 : (OII ∘ OI) ≡ λ x → x
  Δ₂D4 : (OII ∘ O2) ≡ λ x → x
  Δ₂D5 : (OII ∘ I2) ≡ λ x → I


  Δ₃ : Set
  I23 : Δ₂ → Δ₃
  O23 : Δ₂ → Δ₃
  OI3 : Δ₂ → Δ₃
  OI2 : Δ₂ → Δ₃
  --axioms for face maps of Δ₂
  Δ₂F1 : (x : Δ₁) → ((I23 (OI x)) ≡ (OI2 (I2 x)))
  Δ₂F2 : (x : Δ₁) → ((I23 (O2 x)) ≡ (OI3 (I2 x)))
  Δ₂F3 : (x : Δ₁) → ((I23 (I2 x)) ≡ (O23 (I2 x)))
  Δ₂F4 : (x : Δ₁) → ((OI3 (O2 x)) ≡ (O23 (O2 x)))
  Δ₂F5 : (x : Δ₁) → ((OI3 (OI x)) ≡ (OI2 (I2 x)))
  Δ₂F6 : (x : Δ₁) → ((O23 (OI x)) ≡ (OI2 (O2 x)))

  --Degeneracy maps for Δ₃, where
  --OI23 →
  OOI2 : Δ₃ → Δ₂
  OII2 : Δ₃ → Δ₂
  OI22 : Δ₃ → Δ₂

  -- 12 axioms for degen maps of Δ₃
  Δ₃D1 : (OOI2 ∘ I23) ≡ λ x → x
  Δ₃D2 : (OII2 ∘ I23) ≡ (I2 ∘ OOI)
  Δ₃D3 : (OI22 ∘ I23) ≡ (I2 ∘ OII)
  Δ₃D4 : (OOI2 ∘ O23) ≡ λ x → x
  Δ₃D5 : (OII2 ∘ O23) ≡ λ x → x
  Δ₃D6 : (OI22 ∘ O23) ≡ (O2 ∘ OII)
  Δ₃D7 : (OOI2 ∘ OI3) ≡ (O2 ∘ OOI)
  Δ₃D8 : (OII2 ∘ OI3) ≡ λ x → x
  Δ₃D9 : (OI22 ∘ OI3) ≡ λ x → x
  Δ₃D10 : (OOI2 ∘ OI2) ≡ (OI ∘ OOI)
  Δ₃D11 : (OII2 ∘ OI2) ≡ (OI ∘ OII)
  Δ₃D12 : (OI22 ∘ OI2) ≡ λ x → x

_≤_ : Δ₁ → Δ₁ → Set
x ≤ y = x == (x ⊓ y)

-- Defining Hom Types taken from Dirinterval
Hom : {l : Level} (A : Set l) (a0 a1 : A) → Set l
Hom A a0 a1 = Σ (λ (p : Δ₁ → A) → (p O == a0) × ((p I) == a1))

apHom : ∀ {l} {A B : Set l} {a0 a1 : A} (f : A → B) → Hom A a0 a1 → Hom B (f a0) (f a1)

apHom {_} {A} {B} {a0} {a1} f (h , a0eq , a1eq) = (λ (D : Δ₁) → f (h D)) , ap f a0eq , ap f a1eq
--apHom {_} {A} {B} {a0} {a2} f (h , id , id) = (λ (D : Δ₁) → f (h D)) , id , id
--apHom {_} {A} {B} {.(h O)} {.(h I)} f (h , id , id) = (λ (D : Δ₁) → f (h D)) , id , id

-- To define y ≤ x


Triangle : ∀ {l} (A : Set l) {a0 a1 a2 : A} → Hom A a0 a1 → Hom A a1 a2 → Hom A a0 a2 → Set l
Triangle A p q r =
  Σ λ (f : (x : Δ₁) (y : Δ₁) → y ≤ x → A) →
   ((x : Δ₁) → f x O id == fst p x) ×
   (((y : Δ₁) → f I y id == fst q y) ×
   ((z : Δ₁) → f z z id == fst r z))

Singleton : ∀ {l} (A : Set l) → Set l
Singleton A = Σ λ (a : A) →  ∀ (x : A) → a == x

-- hasDHCom  --------------------------------------------------------------------
isSegal : ∀ {l} (A : Set l) → Set l
isSegal A = {a0 a1 a2 : A} (p : Hom A a0 a1) (q : Hom A a1 a2) → Singleton (Σ λ r → Triangle A p q r)

-- ap (λ f → f x) ?
×Segal : ∀ {l} {A B : Set l} → isSegal A → isSegal B → isSegal (A × B)
×Segal {_} {A} {B} SegalA SegalB {a0 , b0} {a1 , b1} {a2 , b2} p q =
  (comp ,  (λ (x y : Δ₁) → λ (y≤x : y ≤ x) →
  (fst TriA) x y y≤x ,  (fst TriB) x y y≤x) ,
  (λ x → ×= (fst (snd TriA) x) (fst (snd TriB) x)) ,
  (λ y →  ×= (fst (snd (snd TriA)) y) (fst (snd (snd TriB)) y)) ,
  λ z → ×= (snd (snd (snd TriA)) z) (snd (snd (snd TriB)) z) ) ,
  λ TriAB → pair= (pair= (λ= λ x → ×= (ap (λ z → z x) (ap fst (ap fst (FuncA (ABTriA TriAB)))) )
  (ap (λ z → z x) (ap fst (ap fst (FuncB (ABTriB TriAB)))))) (×= uip uip))
  (pair= (λ= λ x →  λ= λ y → λ= λ y≤x →
  ×= (ap {M = (transport (Triangle (A × B) p q)
      (pair= (λ= (λ x₁ → ×= (ap (λ z → z x₁) (ap fst (ap fst (FuncA (ABTriA TriAB)))))
           (ap (λ z → z x₁) (ap fst (ap fst (FuncB (ABTriB TriAB)))))))
       (×= uip uip))
      ((λ x₁ y₁ y≤x₁ → fst TriA x₁ y₁ y≤x₁ , fst TriB x₁ y₁ y≤x₁) ,
       (λ x₁ → ×= (fst (snd TriA) x₁) (fst (snd TriB) x₁)) ,
       (λ y₁ → ×= (fst (snd (snd TriA)) y₁) (fst (snd (snd TriB)) y₁)) ,
       (λ z → ×= (snd (snd (snd TriA)) z) (snd (snd (snd TriB)) z))))} {(snd TriAB)} (λ tri → fst ((fst tri) x y y≤x))
       ( het-to-hom ({!hom-to-het (FuncB (ABTriB TriAB)) !} ∘h  transport-=h (Triangle (A × B) p q)
       (pair=
       (λ=
        (λ x₁ →
           ×= (ap (λ z → z x₁) (ap fst (ap fst (FuncA (ABTriA TriAB)))))
           (ap (λ z → z x₁) (ap fst (ap fst (FuncB (ABTriB TriAB)))))))
       (×= uip uip)))))
  {!ap (λ tri → snd (tri x y y≤x)!} )
  ( ×= (λ= λ x → uip )
  (×= (λ= λ y → uip)
  (λ= λ z → uip))))
  {-pair= (pair= (  λ= λ x → ×= (ap {M = λ x → fst (fst comp x)}{λ x → fst (fst (fst TriAB) x)} (λ f → f x) {! FuncA ?!}) {!ap !}) (×= uip  uip))
  (pair= {! (FuncB (ABTriB TriAB))!}
  (×= {! fst comp!} (×= {! fst (fst (fst (SegalA (apHom fst p) (apHom fst q))))!} {!fst comp!})))-}
  {-transport-=h (Triangle (A × B) p q)
       (pair=
       (λ=
        (λ x₁ →
           ×= (ap (λ z → z x₁) (ap fst (ap fst (FuncA (ABTriA TriAB)))))
           (ap (λ z → z x₁) (ap fst (ap fst (FuncB (ABTriB TriAB)))))))
       (×= uip uip))


  (ap {M = fst (transport (Triangle (A × B) p q)
      (pair=
       (λ=
        (λ x₁ →
           ×= (ap (λ z → z x₁) (ap fst (ap fst (FuncA (ABTriA TriAB)))))
           (ap (λ z → z x₁) (ap fst (ap fst (FuncB (ABTriB TriAB)))))))
       (×= uip uip))
      ((λ x₁ y₁ y≤x₁ → fst TriA x₁ y₁ y≤x₁ , fst TriB x₁ y₁ y≤x₁) ,
       (λ x₁ → ×= (fst (snd TriA) x₁) (fst (snd TriB) x₁)) ,
       (λ y₁ → ×= (fst (snd (snd TriA)) y₁) (fst (snd (snd TriB)) y₁)) ,
       (λ z → ×= (snd (snd (snd TriA)) z) (snd (snd (snd TriB)) z))))}
       {fst (snd TriAB)} (λ tri → fst (tri x y y≤x))
       ( het-to-hom ({!!} ∘h ap=o {!!}
       {M = (transport (Triangle (A × B) p q)
           (pair=
            (λ=
             (λ x₂ →
                ×= (ap (λ z → z x₂) (ap fst (ap fst (FuncA (ABTriA TriAB)))))
                (ap (λ z → z x₂) (ap fst (ap fst (FuncB (ABTriB TriAB)))))))
            (×= uip uip))
           ((λ x₂ y₁ y≤x₁ → fst TriA x₂ y₁ y≤x₁ , fst TriB x₂ y₁ y≤x₁) ,
            (λ x₂ → ×= (fst (snd TriA) x₂) (fst (snd TriB) x₂)) ,
            (λ y₁ → ×= (fst (snd (snd TriA)) y₁) (fst (snd (snd TriB)) y₁)) ,
            (λ z → ×= (snd (snd (snd TriA)) z) (snd (snd (snd TriB)) z))))} fst fst hid {!!})) )
  -}
  -- (apdo snd (FuncA (ABTriA TriAB)))
  --ap snd (FuncB (ABTriB TriAB))
  where

  compA : Hom A a0 a2
  compA = fst (fst (SegalA (apHom fst p) (apHom fst q)))

  compB : Hom B b0 b2
  compB = fst (fst (SegalB (apHom snd p) (apHom snd q)))

  ABTriA : Σ (Triangle (A × B) p q) → Σ (Triangle A (apHom fst p) (apHom fst q))
  ABTriA TriAB = apHom fst (fst TriAB) ,
    ((λ (x y : Δ₁) → λ (y≤x : y ≤ x) → fst((fst (snd TriAB)) x y y≤x))) ,
    (λ x → ×=A ((fst (snd (snd TriAB))) x)) ,
    (λ y → ×=A (fst (snd (snd (snd TriAB))) y)) ,
    λ z →  ×=A (snd (snd (snd (snd TriAB))) z)

  ABTriB : Σ (Triangle (A × B) p q) → Σ (Triangle B (apHom snd p) (apHom snd q))
  ABTriB TriAB = apHom snd (fst TriAB) ,
    ( ((λ (x y : Δ₁) → λ (y≤x : y ≤ x) → snd((fst (snd TriAB)) x y y≤x)))) ,
    (λ x → ×=B ((fst (snd (snd TriAB))) x)) ,
    (λ y → ×=B (fst (snd (snd (snd TriAB))) y)) ,
    λ z →  ×=B (snd (snd (snd (snd TriAB))) z)

  comp : Hom (A × B) (a0 , b0) (a2 , b2)
  comp = (λ (D : Δ₁) → ((fst compA) D) , ((fst compB) D)) ,
    (×= (fst ( snd compA )) (fst ( snd compB ))) ,
    (×= (snd (snd compA)) (snd (snd compB)))

  TriA : Triangle A (apHom fst p) (apHom fst q) compA
  TriA = (snd (fst (SegalA (apHom fst p) (apHom fst q))))

  TriB : Triangle B (apHom snd p) (apHom snd q) compB
  TriB = (snd (fst (SegalB (apHom snd p) (apHom snd q))))

  FuncA : (x : Σ (Triangle A (apHom fst p) (apHom fst q))) → fst (SegalA (apHom fst p) (apHom fst q)) == x
  FuncA = (snd (SegalA (apHom fst p) (apHom fst q)))

  FuncB : (x : Σ (Triangle B (apHom snd p) (apHom snd q))) → fst (SegalB (apHom snd p) (apHom snd q)) == x
  FuncB = (snd (SegalB (apHom snd p) (apHom snd q)))

ΠSegal : ∀ {l} {A : Set l} {B : A →  Set l} → isSegal A → ((x : A) → isSegal (B x)) → isSegal ((x : A) → B x)
ΠSegal {_} {A} {B} SegalA DSegalB {Dbx0} {Dbx1} {Dbx2} p q  =
  (comp ,  ( (λ (x y : Δ₁) → λ (y≤x : y ≤ x) → λ a →  (fst (TriBx a)) x y y≤x)) ,
  (λ x → λ= λ a → (fst (snd (TriBx a))) x) ,
  (λ y → λ= λ a → (fst (snd (snd (TriBx a)))) y) ,
  (λ z → λ= λ a → (snd (snd (snd (TriBx a)))) z)) ,
  λ TriABx → pair= (pair= (λ= λ d → λ= λ a →  ap (λ bx → bx d) (ap fst (ap fst (FuncBx a ((ABxTriBx TriABx) a)))) ) (×= uip uip))
  (pair= (λ= λ x → λ= λ y →  λ= λ y≤x →  λ= λ a →
   ap {M = (transport (Triangle ((x₁ : A) → B x₁) p q)
       (pair=
        (λ=
         (λ d →
            λ=
            (λ a₁ →
               ap (λ bx → bx d)
               (ap fst (ap fst (FuncBx a₁ (ABxTriBx TriABx a₁)))))))
        (×= uip uip))
       ((λ x₁ y₁ y≤x₁ a₁ → fst (TriBx a₁) x₁ y₁ y≤x₁) ,
        (λ x₁ → λ= (λ a₁ → fst (snd (TriBx a₁)) x₁)) ,
        (λ y₁ → λ= (λ a₁ → fst (snd (snd (TriBx a₁))) y₁)) ,
        (λ z → λ= (λ a₁ → snd (snd (snd (TriBx a₁))) z))))} {(snd TriABx)} (λ tri → (fst tri) x y y≤x a)
        (het-to-hom ( {!fst  (snd (snd (TriBx a))) !} ∘h transport-=h
        (Triangle ((x₁ : A)→ B x₁) p q) ( pair= (λ= ( (λ x₁ →  λ= λ a →
         ap (λ tri → tri x₁) (ap fst (ap fst (FuncBx a (ABxTriBx TriABx a)))))) )
        (×= uip uip)))) )
  (×= (λ= λ x → uip) (×= (λ= λ y → uip) (λ= λ z →  uip))))  where

  --ap snd (FuncBx a ((ABxTriBx TriABx) a))

  compBx : (x : A) → Hom (B x) (Dbx0 x) (Dbx2 x)
  compBx a = fst (fst ((DSegalB a) (apHom (λ (bx : (x : A) → B x) → bx a) p) (apHom (λ (bx : (x : A) → B x) → bx a) q)))

  TriBx : (x : A) → Triangle (B x) (apHom (λ (bx : (x : A) → B x) → bx x) p) (apHom (λ (bx : (x : A) → B x) → bx x) q) (compBx x)
  TriBx a = snd (fst ((DSegalB a) (apHom (λ (bx : (x : A) → B x) → bx a) p) (apHom (λ (bx : (x : A) → B x) → bx a) q)))

  ABxTriBx : Σ (Triangle ((x : A) → B x) p q) → ((x : A) → Σ (Triangle (B x) (apHom (λ bx → bx x) p) (apHom (λ bx → bx x) q)))
  ABxTriBx TriABx = λ a → apHom (λ bx → bx a) (fst TriABx) ,
    (λ x y → λ y≤x → ((fst (snd TriABx)) x y y≤x) a) ,
    (λ x → ap (λ bx → bx a) ((fst (snd (snd TriABx))) x)) ,
    (λ y →  ap (λ bx → bx a) ((fst(snd (snd (snd TriABx)))) y)) ,
    λ z → ap (λ bx → bx a) ((snd(snd (snd (snd TriABx)))) z)

  FuncBx : (a : A) → (x : Σ (Triangle (B a) (apHom (λ bx → bx a) p) (apHom (λ bx → bx a) q))) →
    fst (DSegalB a (apHom (λ bx → bx a) p) (apHom (λ bx → bx a) q)) == x
  FuncBx a = snd ((DSegalB a) (apHom (λ (bx : (x : A) → B x) → bx a) p) (apHom (λ (bx : (x : A) → B x) → bx a) q))

  comp : Hom ((x : A) → B x) Dbx0 Dbx2
  comp = ( λ (d : Δ₁) → λ (x : A) → fst (compBx x) d) , ( λ= λ x → fst (snd (compBx x)) ) , λ= λ x → snd (snd (compBx x))

{-
Functional Extension in CTT
I → (A → B)
A → (I → B)

(p : (x : A) → Path (B x) (f x) (g x))
λ (i: I) (x : A) . p x i : Path ((x : A) → B x) f g
λ x . f x
≡ f
λ x . g x
-}
{-
{x0 x1 x2 : X} {y0 y1 y2 : Y}
  (p : Hom (X × Y) (x0 × y0) (x1 × y1))
  (q : Hom (X × Y) (x1 × y1) (x2 × y2)) →
  Singleton (Σ λ r → Triangle (X × Y) p q r)
-}

  -- Defining objects; finite, non-empty, totally ordered sets.
  -- bounding n to be 0-2 for the time being
  -- Objects are going to be [n] = [0...n] where n ≤ 3
  -- Interval to Δ


-- For degenerate cases, we dispense with uniqueness but maintain
-- order preserving functions f: [m] → [n] where m ≤ n

-- Δ₀
-- id: {0} → {0}
-- δ₀: {0} → {[], 1}
-- δ₁: {0} → {0, []}

-- Δ₁
-- σ₁: {0, 1} → {0, 0}
-- id: {0, 1} → {0, 1}
-- δ₀: {0, 1} → {[], 1, 2}
-- δ₁: {0, 1} → {0, [], 2}
-- δ₂: {0, 1} → {0, 1, []}

-- Δ₂
-- σ₀: {0, 1, 2} → {0, 0, 1}
-- σ₁: {0, 1, 2} → {0, 1, 1}
---------------------------------------------------
-- id:{0, 1, 2} → {0, 1, 2}
-- id: σ₁ → δ₁
-- id₁: {0, 1, 2} → {0, 1, 1} → {0, 1, 2}
---------------------------------------------------
-- δ₀:{0, 1, 2} → {[], 1, 2, 3}
-- δ₁:{0, 1, 2} → {0, [], 2, 3}
-- δ₂:{0, 1, 2} → {0, 1, [], 3}
-- δ₃:{0, 1, 2} → {0, 1, 2, []}

-- Δ₃
--σ₀: {0, 1, 2, 3} → {0, 0, 1, 2}
--σ₁: {0, 1, 2, 3} → {0, 1, 1, 2}
--σ₂: {0, 1, 2, 3} → {0, 1, 2, 2}
-- id:{0, 1, 2, 3} → {0, 1, 2, 3}

-- Face maps input as interval; Take line. IO → Δ
-- Looking at the axioms used for connections in either dedekind cube or demorgan cube
-- Ed Morehouse: Summary of
-- Write down morphisms in Orton Pitts; (FOCUS ON DIRECTION) ; Unique factorization

-- Truncated base with finite dimensions can potentially have syntax with Reedy categories to define
-- types and terms because we can define presheaves by inductions. (Reedy Category Idea)

-- Partial Univalence in n trucated _ Theory : Christian Sattler and Andrea V.


-- Every morphism factors as
-- Reedy category

-- Morphisms are order preserving as well
-- Face map: dᵢ = Xdⁱ: Xₙ → Xₙ-1 ∀ 0 ≤ i ≤ n
-- Degeneracy map: Sᵢ:Xₙ → Xₙ1 ∀ 0 ≤ i ≤ n

-- Yoneda Embedding
--Let ∁ be a category, and let X and Y be objects of ∁. There is
-- a natural bijection of sets: Homₑ(X, Y) ≅ Hom[Cop, Set](Homₑ(-, X), Homₑ(-, Y))
--between the morphisms of ∁ from X to Y and the natural transformations from the presheaf Hom∁(-, X)
--∁ᵒᵖ→ Set represented by X to the presheaf Homₑ(X, -) : Cᵒᵖ → Set

--Yoneda embedding of the objects (Types)
--Yoneda embedding of the morphisms (terms)
--Relation on morphisms to get compositions (Equations on the terms)

-- this not
-- morphisms from square to the interval
-- Taking 2d point

--simplicial presheafs are a full subcategory of dedekind cubes.
--Everything directed is simplicial. Dedekind cubes are directed.

-- Equations on terms, equations on moprhisms.

{-
In lecture 6, we created a formula from a program
yes
you don’t have to apply any decision procedure
you are right
the program will always be correct
which means the assertion won’t fail
so, what does this say about the formula?
you are right — the formula will be unsatisfiable!
This is all part a is asking about, just write the formula
correct!
yes, flip the assertion!
part b is also interesting — here, we want the same formula to become satisfiable. how do you arrange that?
you are on the right track, change something in the interpretation (which will become non-standard) so that the same formula becomes satisfiable
what about part c?
do you understand the question?
check a discussion thread on Ed for part c
you can think about it, and write to me (or the TAs) if you get stuck
Great!
You are welcome
let me pull up the demo and I’ll share my screen

-}
