
----
---- Práctica 3: Estructura de ω-grupoide y transporte
----

open import Data.Empty
       using (⊥; ⊥-elim)
open import Data.Bool
       using (Bool; true; false)
open import Data.Nat
       using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties
       using (+-comm)
open import Data.Product
       using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
       using (_≡_; refl; cong; sym)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import practica2 using (ind≡)


---- Parte A ----

-- Considerar las siguientes definiciones de la composición de caminos (transitividad)
-- e inversa de un camino (simetría). Son equivalentes a sym y trans pero cambiando
-- la notación.

_∙_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

_⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

-- A.1) Demostrar que la reflexividad es el neutro de la composición de caminos
-- a izquierda y a derecha.

∙-refl-left : {A : Set} {x y : A} {p : x ≡ y}
            → refl ∙ p ≡ p
∙-refl-left {A} {x} {y} {p} = ind≡ {C = λ x y p → refl ∙ p ≡ p} (λ x → refl) x y p 

∙-refl-right : {A : Set} {x y : A} {p : x ≡ y}
             → p ∙ refl ≡ p
∙-refl-right {A} {x} {y} {p} = ind≡ {C = λ x y p -> p ∙ refl ≡ p} (λ x -> refl) x y p


-- A.2) Demostrar que la composición de caminos es asociativa.

-- Algunos lemas auxiliares recursivos :D
-- (refl ∙ q) ∙ r ≡ refl ∙ (q ∙ r)
∙-assoc-refl-refl : {A : Set} {z w : A} {q : z ≡ w} -> ((refl ∙ refl) ∙ q) ≡ (refl ∙ (refl ∙ q))
∙-assoc-refl-refl {A} {z} {w} {q} = 
    begin
        ((refl ∙ refl) ∙ q)
    ≡⟨ refl ⟩ 
        refl ∙ q
    ≡⟨ sym (∙-refl-left) ⟩
        refl ∙ (refl ∙ q)
    ∎

∙-assoc-refl-left : {A : Set} {y z w : A} {q : y ≡ z} {r : z ≡ w} -> (refl ∙ q) ∙ r ≡ refl ∙ (q ∙ r)
-- En la (λ y z q w r ) tenemos "λ y y refl" como parametros
∙-assoc-refl-left {A} {y} {z} {w} {q} {r} = 
    ind≡ 
    {C = λ y z q -> (w : A) (r : z ≡ w) -> (refl ∙ q) ∙ r ≡ refl ∙ (q ∙ r)} 
    --?0 : (a w₁ : A) (r₁ : a ≡ w₁) →
    --((refl ∙ refl) ∙ r₁) ≡ (refl ∙ (refl ∙ r₁))
    (λ y z q -> ∙-assoc-refl-refl) y z q w r

∙-assoc : {A : Set} {x y z w : A} {p : x ≡ y} {q : y ≡ z} {r : z ≡ w}
        → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙-assoc {A} {x} {y} {z} {w} {p} {q} {r} = ind≡ 
    {C = λ x y p → (z w : A) (q : y ≡ z) (r : z ≡ w) → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)} 
    (λ x z w q r → ∙-assoc-refl-left) 
    x y p z w q r

-- A.3) Demostrar que la inversa es efectivamente la inversa, a izquierda y a derecha.

∙-⁻¹-left : {A : Set} {x y : A} {p : x ≡ y}
            → (p ⁻¹) ∙ p ≡ refl
∙-⁻¹-left {A} {x} {y} {p} = ind≡ {C = λ x y p -> (p ⁻¹) ∙ p ≡ refl} (λ x -> refl) x y p

∙-⁻¹-right : {A : Set} {x y : A} {p : x ≡ y}
            → p ∙ (p ⁻¹) ≡ refl
∙-⁻¹-right {A} {x} {y} {p} = ind≡ {C = λ x y p -> p ∙ (p ⁻¹) ≡ refl} (λ x -> refl) x y p

-- A.4) Usando las propiedades anteriores y sin hacer pattern matching sobre los caminos,
-- completar la demostración de que la inversa es involutiva:

⁻¹-involutive : {A : Set} {x y : A} {p : x ≡ y}
              → (p ⁻¹) ⁻¹ ≡ p
⁻¹-involutive {A} {x} {y} {p} =
    (p ⁻¹) ⁻¹
  ≡⟨ sym (∙-refl-right) ⟩
    ((p ⁻¹) ⁻¹) ∙ refl
  ≡⟨ cong (λ z -> ((p ⁻¹) ⁻¹) ∙ z) (sym (∙-⁻¹-left)) ⟩
    ((p ⁻¹) ⁻¹) ∙ ((p ⁻¹) ∙ p)
  ≡⟨ sym ∙-assoc  ⟩
    (((p ⁻¹) ⁻¹) ∙ (p ⁻¹)) ∙ p
  ≡⟨ cong (λ z -> z ∙ p) (∙-⁻¹-left) ⟩
    refl ∙ p
  ≡⟨ ∙-refl-left ⟩
    p
  ∎

-- A.5) Usando las propiedades anteriores y sin hacer pattern matching sobre los caminos,
-- demostrar las siguientes propiedades de cancelación a izquierda y a derecha:

∙-cancel-left : {A : Set} {x y z : A} {p : x ≡ y} {q q' : y ≡ z}
             → p ∙ q ≡ p ∙ q'
             → q ≡ q'
∙-cancel-left {A} {x} {y} {z} {p} {q} {q'} pq≡pq' =
    begin
        q
    ≡⟨ sym (∙-refl-left) ⟩ 
        refl ∙ q
    ≡⟨ cong (λ z -> z ∙ q) (sym ∙-⁻¹-left) ⟩
        ((p ⁻¹) ∙ p) ∙ q      -- (ayuda)
    ≡⟨ ∙-assoc ⟩
        (p ⁻¹) ∙ (p ∙ q)
    ≡⟨ cong (λ z -> (p ⁻¹) ∙ z) (pq≡pq')⟩ 
        (p ⁻¹) ∙ (p ∙ q')
    ≡⟨ sym (∙-assoc) ⟩ 
        ((p ⁻¹) ∙ p) ∙ q'
    ≡⟨ cong (λ z -> z ∙ q') (∙-⁻¹-left) ⟩ 
        refl ∙ q'
    ≡⟨ ∙-refl-left ⟩ 
        q'
    ∎

∙-cancel-right : {A : Set} {x y z : A} {p p' : x ≡ y} {q : y ≡ z}
               → p ∙ q ≡ p' ∙ q
               → p ≡ p'
∙-cancel-right {A} {x} {y} {z} {p} {p'} {q} pq≡p'q = 
    begin
        p
    ≡⟨ sym (∙-refl-right) ⟩
        p ∙ refl
    ≡⟨ cong (λ z -> p ∙ z) (sym ∙-⁻¹-right) ⟩
        p ∙ (q ∙ (q ⁻¹))
    ≡⟨ sym ∙-assoc ⟩
        (p ∙ q) ∙ (q ⁻¹)
    ≡⟨ cong (λ z -> z ∙ (q ⁻¹)) (pq≡p'q) ⟩ 
        (p' ∙ q) ∙ (q ⁻¹)
    ≡⟨ ∙-assoc ⟩
        p' ∙ (q ∙ (q ⁻¹))
    ≡⟨ cong (λ z -> p' ∙ z) (∙-⁻¹-right) ⟩
        p' ∙ refl
    ≡⟨ ∙-refl-right ⟩ 
        p'
    ∎

-- A.6) Usando las propiedades anteriores y sin hacer pattern matching sobre los caminos,
-- demostrar las siguientes propiedades, que caracterizan a la inversa a izquierda y
-- a derecha:

⁻¹-univ-left : {A : Set} {x y z : A} {p : x ≡ y} {q : y ≡ x}
             → p ∙ q ≡ refl
             → p ≡ q ⁻¹
⁻¹-univ-left {A} {x} {y} {z} {p} {q} pq≡refl = 
    begin
        p
    ≡⟨ sym ∙-refl-right ⟩ 
        p ∙ refl
    ≡⟨ cong (λ z -> p ∙ z) (sym ∙-⁻¹-right) ⟩ 
        p ∙ (q ∙ (q ⁻¹))
    ≡⟨ sym ∙-assoc ⟩ 
        (p ∙ q) ∙ (q ⁻¹) 
    ≡⟨ cong (λ z ->  z ∙ (q ⁻¹)) pq≡refl ⟩ 
        refl ∙ (q ⁻¹) 
    ≡⟨ ∙-refl-left ⟩ 
        q ⁻¹
    ∎

⁻¹-univ-right : {A : Set} {x y z : A} {p : x ≡ y} {q : y ≡ x}
              → p ∙ q ≡ refl
              → q ≡ p ⁻¹
⁻¹-univ-right {A} {x} {y} {z} {p} {q} pq≡refl =
    begin
        q
    ≡⟨ sym ∙-refl-left ⟩
        refl ∙ q
    ≡⟨ cong (λ z -> z ∙ q) (sym ∙-⁻¹-left) ⟩ 
        ((p ⁻¹) ∙ p) ∙ q
    ≡⟨ ∙-assoc ⟩ 
        (p ⁻¹) ∙ (p ∙ q)
    ≡⟨ cong (λ z -> (p ⁻¹) ∙ z) (pq≡refl) ⟩ 
        (p ⁻¹) ∙ refl
    ≡⟨ ∙-refl-right ⟩ 
        p ⁻¹
    ∎

-- A.7) Usando las propiedades anteriores y sin hacer pattern matching sobre los caminos,
-- demostrar la siguiente propiedad de conmutación entre la composición de caminos y
-- la inversa:

∙-⁻¹-comm-aux : {A : Set} {x y z : A} {p : x ≡ y} {q : y ≡ z} -> (((p ∙ q) ⁻¹) ⁻¹) ∙ (((q ⁻¹) ∙ (p ⁻¹))) ≡ refl
∙-⁻¹-comm-aux {A} {x} {y} {z} {p} {q} =
    begin
       (((p ∙ q) ⁻¹) ⁻¹) ∙ ((q ⁻¹) ∙ (p ⁻¹))
    ≡⟨ cong (λ z -> z ∙ ((q ⁻¹) ∙ (p ⁻¹)) ) (⁻¹-involutive) ⟩
        (p ∙ q) ∙ ((q ⁻¹) ∙ (p ⁻¹))
    ≡⟨ sym ∙-assoc ⟩ 
        ((p ∙ q) ∙ (q ⁻¹)) ∙ (p ⁻¹)
    ≡⟨ cong (λ z -> z ∙ (p ⁻¹)) (∙-assoc) ⟩  
        (p ∙ (q ∙ (q ⁻¹))) ∙ (p ⁻¹)
    ≡⟨ cong (λ z -> (p ∙ z) ∙ (p ⁻¹)) (∙-⁻¹-right) ⟩  
        (p ∙ refl) ∙ (p ⁻¹)
    ≡⟨ cong (λ z -> z ∙ (p ⁻¹)) (∙-refl-right) ⟩  
        p ∙ (p ⁻¹)
    ≡⟨ ∙-⁻¹-right ⟩ 
        refl
    ∎

∙-⁻¹-comm : {A : Set} {x y z : A} {p : x ≡ y} {q : y ≡ z}
             → (p ∙ q)⁻¹ ≡ (q ⁻¹) ∙ (p ⁻¹)
∙-⁻¹-comm {A} {x} {y} {z} {p} {q} = 
    begin
        ((p ∙ q) ⁻¹)
    ≡⟨ sym (⁻¹-involutive {p = (p ∙ q) ⁻¹}) ⟩
        (((((p ∙ q) ⁻¹) ⁻¹)) ⁻¹)
    ≡⟨ sym (⁻¹-univ-right {A} {x} {z} {x} {p = ((p ∙ q) ⁻¹) ⁻¹} {q = (q ⁻¹) ∙ (p ⁻¹)} (∙-⁻¹-comm-aux)) ⟩
        (q ⁻¹) ∙ (p ⁻¹)
    ∎


---- Parte B ----

-- Usamos los booleanos para representar bits (false = 0 ; true = 1).
-- Consideramos la siguiente función auxiliar:
_+bit_ : Bool → ℕ → ℕ
false +bit n = n
true  +bit n = suc n

+bit-suc : {n : ℕ} {b : Bool} -> suc (b +bit n) ≡ b +bit (suc n)
+bit-suc {n} {false} = refl
+bit-suc {n} {true} = refl

-- Consideramos el siguiente tipo de datos para codificar naturales en binario:
data Bin : Set where
  binzero : Bin
  addbit  : Bin → Bool → Bin

-- Donde:
-- ─ b0 representa el 0
-- ─ Si x : Bin, entonces addbit x b es el número que resulta de agregar el bit b a la derecha
--   (es decir, "b +bit (2 * x)").
-- Por ejemplo,
--   addbit (addbit (addbit binzero true) false) false
-- codifica el número (100)₂ = 4.

-- B.1) Definir la función que convierte un número representado en binario a natural:
bin2nat : Bin → ℕ
bin2nat binzero      = zero
bin2nat (addbit x false) = bin2nat x + bin2nat x
bin2nat (addbit x true) = suc (bin2nat x + bin2nat x)

-- B.2) Definir la función sucesor sobre números naturales representados en binario:
binsuc : Bin → Bin
binsuc binzero          = addbit binzero true
binsuc (addbit x false) = addbit x true
binsuc (addbit x true)  = addbit (binsuc x) false       --propaga el 0 (carry!!!)

-- B.3) Usando binsuc, definir la función que convierte un número natural a su representación binaria:
nat2bin : ℕ → Bin
nat2bin zero = binzero
nat2bin (suc n) = binsuc (nat2bin n)


bin2nat-binsuc-suc : {bin : Bin} -> bin2nat (binsuc bin) ≡ suc (bin2nat bin)
bin2nat-binsuc-suc {binzero} = refl
bin2nat-binsuc-suc {addbit x true} = 
    begin
        bin2nat (binsuc (addbit x true))
    ≡⟨ refl ⟩
        bin2nat (addbit (binsuc x) false) 
    ≡⟨ refl ⟩ 
        bin2nat (binsuc x) + bin2nat (binsuc x)
    ≡⟨ cong (λ z -> z + bin2nat (binsuc x)) (bin2nat-binsuc-suc {x})⟩ 
        suc (bin2nat x) + bin2nat (binsuc x)
    ≡⟨ cong (λ z -> suc (bin2nat x) + z) (bin2nat-binsuc-suc {x})⟩ 
        suc (bin2nat x) + suc (bin2nat x)
    ≡⟨ refl ⟩ 
        suc (bin2nat x + suc (bin2nat x))
    ≡⟨ cong suc (+-comm (bin2nat x) (suc (bin2nat x))) ⟩ 
        suc (suc (bin2nat x + bin2nat x))
    ≡⟨ cong suc (sym refl) ⟩ 
        suc (bin2nat (addbit x true))
    ∎
bin2nat-binsuc-suc {addbit x false} = refl 


-- B.4) Demostrar que bin2nat es la inversa a izquierda de nat2bin:
nat2bin2nat : (n : ℕ) → bin2nat (nat2bin n) ≡ n
nat2bin2nat zero = refl 
    -- begin
    --     bin2nat (nat2bin zero)
    -- ≡⟨ refl ⟩
    --     bin2nat (binzero)
    -- ≡⟨ refl ⟩ 
    --     zero
    -- ∎
nat2bin2nat (suc n) = 
    begin 
        bin2nat (nat2bin (suc n))
    ≡⟨ refl ⟩ 
        bin2nat (binsuc (nat2bin n))
    ≡⟨ bin2nat-binsuc-suc {nat2bin n}⟩ 
        suc (bin2nat (nat2bin n))
    ≡⟨ cong (λ z -> suc z) (nat2bin2nat n) ⟩ 
        suc n
    ∎

double-suc-distributive : {q : ℕ} -> suc (suc (q + q)) ≡ suc q + suc q
double-suc-distributive {q} = 
    begin
        suc (suc (q + q))
    ≡⟨ cong suc refl ⟩
        suc (suc q + q)
    ≡⟨ cong suc (+-comm (suc q) q) ⟩
        suc (q + suc q)
    ≡⟨ refl ⟩
        suc q + suc q 
    ∎

aux2 : {n q : ℕ} {r : Bool} -> n ≡ r +bit (q + q) -> suc (suc n) ≡ r +bit (suc q + suc q)
aux2 {n} {q} {r} dem = 
    begin
        suc (suc n)
    ≡⟨ cong (λ z -> suc (suc z)) dem ⟩
        suc (suc (r +bit (q + q)))
    ≡⟨ cong suc (+bit-suc {q + q} {r}) ⟩ 
        suc (r +bit (suc (q + q)))
    ≡⟨ +bit-suc {suc (q + q)} {r} ⟩ 
        r +bit (suc (suc (q + q)))
    ≡⟨ cong (λ z -> r +bit z) double-suc-distributive ⟩ 
        r +bit (suc q + suc q) 
    ∎

-- B.5) Definir la siguiente función, que descompone un número natural en su cociente y su resto
-- en la división por 2:
divmod2 : (n : ℕ) → Σ[ q ∈ ℕ ] Σ[ r ∈ Bool ] n ≡ r +bit (q + q)
divmod2 zero          = (zero , false , refl)
divmod2 (suc zero)    = (zero , true , refl)
--n≡q+q+r' es de tipo n ≡ (r' +bit (q' + q'))
divmod2 (suc (suc n)) = let (q' , r' , n≡q+q+r') = divmod2 n in
                          (suc q' , r' , aux2 n≡q+q+r')

---- Parte C ----

-- Recordemos el operador de transporte:
transport : {A : Set} (B : A → Set) {x y : A} (p : x ≡ y) → B x → B y
transport _ refl b = b

-- C.1) Demostrar que transportar por la familia (B ∘ f) vía el camino p
-- equivale a transportar por la familia B vía el camino (cong f p).
transport-compose : {A A' : Set} (f : A → A') (B : A' → Set) {x y : A} (p : x ≡ y) (b : B (f x))
           → transport (λ x → B (f x)) p b ≡ transport B (cong f p) b
transport-compose f B refl b = refl

-- C.2) Demostrar que transportar vía la composición de dos caminos
-- equivale a transportar separadamente vía cada uno de ellos.
transport-∙ : {A : Set} (B : A → Set) {x y z : A} (p : x ≡ y) (q : y ≡ z) (b : B x)
           → transport B (p ∙ q) b ≡ transport B q (transport B p b)
transport-∙ B refl refl b = refl

-- C.3) Demostrar que transportar por una familia constante es la identidad.
transport-const : {A : Set} (B₀ : Set) {x y : A} (p : x ≡ y) (b : B₀)
                → transport (λ _ → B₀) p b ≡ b
transport-const B0 refl b = refl

-- C.4) Demostrar que transportar por una familia de caminos corresponde a componer: 
transport-path-left : {A : Set} {x y z : A} (p : x ≡ y) (q : x ≡ z)
                    → transport (λ a → a ≡ z) p q ≡ (p ⁻¹) ∙ q
transport-path-left refl refl = refl

-- C.5) Similar pero con la composición a derecha:
transport-path-right : {A : Set} {x y z : A} (p : x ≡ y) (q : z ≡ x)
                     → transport (λ a → z ≡ a) p q ≡ q ∙ p
transport-path-right refl refl = refl

---- Parte D ----

-- Definimos una familia `Fin n` indexada por `n : ℕ`.
-- Informalmente, `Fin n` es el tipo finito cuyos elementos son {0, 1, ..., n}.
data Fin : (n : ℕ) → Set where
  -- finZero es el único habitante de Fin 1
  finZero : Fin zero
  -- Si x es un habitante de Fin n,
  -- entonces finSuc x es un habitante de Fin (suc n).
  finSuc  : {n : ℕ} → Fin n → Fin (suc n)

-- D.1) Definir la suma:
sumaFin : {n m : ℕ} → Fin n → Fin m → Fin (n + m)
-- sumaFin finZero finZero = finZero
-- sumaFin finZero (finSuc y) = finSuc y
-- sumaFin {n} (finSuc x) finZero = transport (λ n -> Fin n) (+-comm zero n) (finSuc x)
-- -- Tomamos Fin (n + m) en el orden que corresponde, 
-- -- y damos la demo de que m + n ≡ n + m
-- --
-- sumaFin {n} {m} (finSuc x) (finSuc y) = transport (λ z -> Fin (n + m)) (+-comm m n) (finSuc (sumaFin x y))

sumaFin {n} {m} finZero    y = y
sumaFin {n} {m} (finSuc x) y = transport (λ _ -> Fin (n + m)) (+-comm m n) (finSuc (sumaFin x y))

-- D.2) Demostrar que la suma es conmutativa:
sumaFin-comm : {n m : ℕ} (x : Fin n) (y : Fin m) → sumaFin x y ≡ transport Fin (+-comm m n) (sumaFin y x)
sumaFin-comm finZero finZero = refl
-- +-comm m zero devuelve m + zero ≡ m. Luego transport Fin (+-comm m zero) es la "identidad" de elementos de Fin m
sumaFin-comm {zero} {m} finZero (finSuc y) = 
    begin
        sumaFin finZero (finSuc y)
    ≡⟨ refl ⟩ 
        finSuc y 
    ≡⟨ ? ⟩
        ?
    ≡⟨ sym (transport-∙ Fin (+-comm zero m) (+-comm m zero) (finSuc (sumaFin y finZero))) ⟩ 
        transport Fin (+-comm m zero) (transport (λ _ -> Fin (m + zero)) (+-comm zero m) (finSuc (sumaFin y finZero)))
    ≡⟨ sym refl ⟩ 
        transport Fin (+-comm m zero) (sumaFin (finSuc y) finZero)
    ∎

sumaFin-comm {(suc n)} {m} (finSuc x) y = 
    begin
        sumaFin (finSuc x) y
    ≡⟨ refl ⟩ 
        transport (λ _ -> Fin (suc n + m)) (+-comm m (suc n)) (finSuc (sumaFin x y))
    ≡⟨ {!   !} ⟩ 
        transport Fin (+-comm m (suc n)) (sumaFin y (finSuc x))
    ∎