
----
---- Práctica 2: Naturales e igualdad
----

open import Data.Empty
       using (⊥; ⊥-elim)
open import Data.Bool
       using (Bool; true; false)
open import Data.Nat
       using (ℕ; zero; suc)
open import Data.Product
       using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
       using (_≡_; refl; sym; trans; cong)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

infixl 20 _+_
infixl 30 _*_

---- Parte A ----

-- Considerar las siguientes definiciones de la suma y el producto:

_+_ : ℕ → ℕ → ℕ
zero  + b = b
suc a + b = suc (a + b)

_*_ : ℕ → ℕ → ℕ
zero  * _ = zero
suc a * b = b + a * b


-- A.1) Demostrar que la suma es asociativa.
+-assoc : {a b c : ℕ} → (a + b) + c ≡ a + (b + c)
+-assoc {zero} {m} {q} = 
  begin
    (zero + m) + q
  ≡⟨ refl ⟩
    m + q
  ≡⟨ refl ⟩
    zero + (m + q)
  ∎
--Recursion hasta que n sea cero!
+-assoc {suc n} {m} {q}  = cong suc (+-assoc {n})

-- A.2) Demostrar que la suma es conmutativa.
-- Sugerencia: demostrar lemas auxiliares que prueben que:
--   a + zero = a
--   a + suc b = suc (a + b)
zeroPlus : { a : ℕ } -> zero + a ≡ a
zeroPlus {zero} = refl
zeroPlus {suc a} = cong suc (zeroPlus {a})

plusZero : { a : ℕ } -> a ≡ a + zero
plusZero {zero} = refl
plusZero {suc a} = cong suc (plusZero {a})

suc-comm-inverse : { a b : ℕ} -> a + suc b ≡ suc (a + b)
suc-comm-inverse {zero} {b} = 
    begin
       zero + suc b
    ≡⟨ refl ⟩
       suc b
    ≡⟨ zeroPlus ⟩
       suc (zero + b)
    ∎
suc-comm-inverse {suc a} {b} = cong suc (suc-comm-inverse {a} {b})

+-comm : {a b : ℕ} → a + b ≡ b + a
+-comm {a} {zero} = 
    begin
       a + zero
    ≡⟨ sym plusZero ⟩
       a
    ≡⟨ zeroPlus ⟩
       zero + a
    ∎
+-comm {a} {suc b} = 
    begin
       a + suc b 
    ≡⟨ suc-comm-inverse ⟩
       suc (a + b)
    ≡⟨ cong suc (+-comm {a} {b}) ⟩
       suc (b + a)
    ≡⟨ refl ⟩ 
       suc b + a
    ∎


*-zero-r : {a : ℕ} -> a * zero ≡ zero
*-zero-r {zero} = refl
*-zero-r {suc a} =
  begin
    suc a * zero
  ≡⟨ refl ⟩ --def de _*_
    zero + a * zero
  ≡⟨ zeroPlus ⟩
    a * zero
  ≡⟨ *-zero-r {a}⟩
    zero
  ∎

sumOfZeroProductIsZero : {a b : ℕ} -> a * zero + b * zero ≡ zero
sumOfZeroProductIsZero {a} {b} =
   begin
      a * zero + b * zero
   --qvq a*zero + b*zero ≡ zero + b*zero
   --para esto, pruebo que aplicandole la funcion lambda esa a ambos lados de
   -- a*zero ≡ zero
   -- obtengo a*zero + b*zero ≡ zero + b*zero
   -- entonces obtengo eso ultimo como resultado, que es lo que queriamos
   ≡⟨ cong (λ x → x + b * zero) (*-zero-r {a}) ⟩
      zero + b * zero
   ≡⟨ zeroPlus ⟩
      b * zero
   ≡⟨ *-zero-r {b} ⟩
      zero
   ∎

-- A.3) Demostrar que el producto distribuye sobre la suma (a izquierda).
*-+-distrib-l : {a b c : ℕ} → (a + b) * c ≡ a * c + b * c
*-+-distrib-l {a} {b} {zero} = 
   begin
      (a + b) * zero
   ≡⟨ *-zero-r {a + b}⟩
      zero
   ≡⟨ sym (sumOfZeroProductIsZero {a} {b})⟩
      a * zero + b * zero
   ∎
*-+-distrib-l {a} {b} {suc c} = {!   !}

*-zero-add : {a : ℕ} -> zero ≡ a * zero
*-zero-add {zero} = refl
*-zero-add {suc a} = sym (*-zero-r {a})

*-suc-r : {a b : ℕ} -> a + a * b ≡ a * suc b
*-suc-r {a} {b} = {!   !}


-- A.4) Demostrar que el producto es asociativo:
*-assoc : {a b c : ℕ} → (a * b) * c ≡ a * (b * c)
*-assoc {a} {b} {zero} = 
   begin
      (a * b) * zero
   ≡⟨ *-zero-r {a * b}⟩
      zero
   ≡⟨ *-zero-add {a}⟩
      a * zero
   ≡⟨ cong (λ x -> a * x) (sym (*-zero-r {b}))⟩
      a * (b * zero)
   ∎ 
*-assoc {a} {b} {suc c} = 
    begin
       (a * b) * suc c
    ≡⟨ {!   !}  ⟩
       (a * b) + (a * b * c)
    ≡⟨ cong (λ z -> (a * b) + z) (*-assoc {a} {b} {c}) ⟩ 
       (a * b) + a * (b * c)
    ≡⟨ cong (λ z -> a * b + a * z) (*-assoc {a} {b} {c})⟩ --Esto esta mal
       a * (b + b * c)
    ≡⟨ cong (λ z -> a * z) (*-suc-r {b} {c}) ⟩ 
       a * (b * suc c)
    ∎

-- A.5) Demostrar que el producto es conmutativo.
-- Sugerencia: demostrar lemas auxiliares que prueben que:
--   a * zero = zero
--   a * suc b = a + a * b
*-comm : {a b : ℕ} → a * b ≡ b * a
*-comm = {!!}

-- A.6) Demostrar que el producto distribuye sobre la suma (a derecha).
-- Sugerencia: usar la conmutatividad y la distributividad a izquierda.
*-+-distrib-r : {a b c : ℕ} → a * (b + c) ≡ a * b + a * c
*-+-distrib-r = {!!}

--------------------------------------------------------------------------------

---- Parte B ----

-- Considerar la siguiente definición del predicado ≤ que dados dos números
-- naturales devuelve la proposición cuyos habitantes son demostraciones de que
-- n es menor o igual que m, y la siguiente función ≤? que dados dos
-- números naturales devuelve un booleano que indica si n es menor o igual que
-- n.

_≤_ : ℕ → ℕ → Set
n ≤ m = Σ[ k ∈ ℕ ] k + n ≡ m

_≤?_ : ℕ → ℕ → Bool
zero  ≤? m     = true
suc _ ≤? zero  = false
suc n ≤? suc m = n ≤? m

-- B.1) Demostrar que la función es correcta con respecto a su especificación.
-- Sugerencia: seguir el esquema de inducción con el que se define la función _≤?_.

≤?-correcta : {n m : ℕ} → (n ≤? m) ≡ true → n ≤ m
≤?-correcta = {!!}

-- B.2) Demostrar que es imposible que el cero sea el sucesor de algún natural:

zero-no-es-suc : {n : ℕ} → suc n ≡ zero → ⊥
zero-no-es-suc = {!!}

-- B.3) Demostrar que la función es completa con respecto a su especificación.
-- Sugerencia: seguir el esquema de inducción con el que se define la función _≤?_.
-- * Para el caso en el que n = suc n' y m = zero, usar el ítem B.2 y propiedades de la suma.
-- * Para el caso en el que n = suc n' y m = suc m', recurrir a la hipótesis inductiva y propiedades de la suma.

≤?-completa : {n m : ℕ} → n ≤ m → (n ≤? m) ≡ true
≤?-completa = {!!}

--------------------------------------------------------------------------------

---- Parte C ----

-- La siguiente función corresponde al principio de inducción en naturales:

indℕ : (C : ℕ → Set)
       (c0 : C zero)
       (cS : (n : ℕ) → C n → C (suc n))
       (n : ℕ)
       → C n
indℕ C c0 cS zero    = c0
indℕ C c0 cS (suc n) = cS n (indℕ C c0 cS n)

-- Definimos el predicado de "menor estricto" del siguiente modo:
_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

-- C.1) Demostrar el principio de inducción completa, que permite recurrir a la hipótesis
-- inductiva sobre cualquier número estrictamente menor.
ind-completa : (C : ℕ → Set)
               (f : (n : ℕ)
                  → ((m : ℕ) → suc m ≤ n → C m)
                  → C n)
               (n : ℕ)
               → C n
ind-completa C f n = {!!}

--------------------------------------------------------------------------------

---- Parte D ----

-- D.1) Usando pattern matching, definir el principio de inducción sobre la
-- igualdad:

ind≡ : {A : Set}
       {C : (a b : A) → a ≡ b → Set}
     → ((a : A) → C a a refl)
     → (a b : A) (p : a ≡ b) → C a b p
ind≡ = {!!}

-- D.2) Demostrar nuevamente la simetría de la igualdad, usando ind≡:

sym' : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym' = {!!}

-- D.3) Demostrar nuevamente la transitividad de la igualdad, usando ind≡:

trans' : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans' = {!!}

-- D.4) Demostrar nuevamente que la igualdad es una congruencia, usando ind≡:

cong' : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong' = {!!}