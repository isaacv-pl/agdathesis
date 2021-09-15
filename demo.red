-- hello world

-- U = universe
-- kan = supports kan operators
-- extension typeinterval shape 
--def path (A : type) (a0 a1 : A) : type =
    --[i] A [i=0 -> a0 | i=1 -> a1]

-- dependent path
def pathd (A : 𝕀 -> type) (a0 : A 0) (a1 : A 1) : type =
    [i] A i [i=0 -> a0 | i=1 -> a1]

def path (A : type) (a0 a1 : A) : type =
    pathd (λ _ -> A) a0 a1

--Extensionality principle for pairs
--def pair-ext (A B : type) (P Q : A × B)
--(α : path _ (P .fst) (Q .fst))
--(β : path _ (P .snd) (Q .snd)) : path _ P Q = 
--λ i -> 
--(α i, β i)

def pair-ext (A : type) (B : A -> type)
(P Q : (x: A) × B x) (α : path A (P .fst) (Q .fst)) 
(β : pathd (λ i -> B (α i)) (P .snd) (Q. snd)) : 
path _ P Q = 
λ i -> 
(α i, β i)

-- Principle of extensionality proofs is that because 

def fun-ext (A B: type) (f g: A -> B) (α : (x : A) -> 
path _ (f x) (g x)) : path  _ f g = 
λ i x -> α x i


