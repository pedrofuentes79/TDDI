
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

*-zero-l : {a : ℕ} -> zero * a ≡ zero
*-zero-l {zero} = refl
*-zero-l {suc a} = refl

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

*-zero-add : {a : ℕ} -> zero ≡ a * zero
*-zero-add {zero} = refl
*-zero-add {suc a} = sym (*-zero-r {a})

*-zero-add-v2 : {a : ℕ} -> zero ≡ zero * a
*-zero-add-v2 {zero} = refl
*-zero-add-v2 {suc a} = sym (*-zero-l {a})

*-1-add-r : {a : ℕ} ->  a * (suc zero) ≡ a
*-1-add-r {zero} = *-zero-r {zero}
*-1-add-r {suc a} = 
   begin
      suc a * suc zero
   ≡⟨ refl ⟩
      suc zero + a * suc zero
   ≡⟨ cong (λ c -> suc zero + c) (*-1-add-r {a}) ⟩ 
      suc zero + a
   ≡⟨ refl ⟩
      suc a
   ∎
+-suc-a-is-suc-zero+a : {a : ℕ} -> suc a ≡ suc zero + a
+-suc-a-is-suc-zero+a {a} = refl

*-suc-r : {a b : ℕ} -> a + a * b ≡ a * suc b
*-suc-r {zero} {b} = 
   begin
      zero + zero * b
   ≡⟨ plusZero {zero * b}⟩
      zero * b
   ≡⟨ *-zero-l {b} ⟩ 
      zero  
   ≡⟨ *-zero-add-v2 {suc b}⟩
      zero * suc b 
   ∎
*-suc-r {suc a} {b} = 
   begin
      suc a + suc a * b
   ≡⟨ cong (λ c -> suc a + c) refl ⟩ 
      suc a + (b + a * b)
   ≡⟨ sym (+-assoc {suc a} {b} {a * b}) ⟩ 
      suc a + b + a * b
   ≡⟨ cong (λ c -> c + b + a * b) (+-suc-a-is-suc-zero+a {a}) ⟩ -- suc a ≡ suc zero + a 
      suc zero + a + b + a * b
-- me hubiese gustado hacer desde aca hasta HI con cong en un solo paso
-- pero me rompia la asociatividad o algo asi...
   ≡⟨ +-assoc {(suc zero + a)} {b} {a * b} ⟩
      suc zero + a + (b + a * b)
   ≡⟨ cong (λ c -> suc zero + a + c) (+-comm {b} {a * b}) ⟩ 
      suc zero + a + (a * b + b)
   ≡⟨ sym (+-assoc {(suc zero + a)} {a * b} {b}) ⟩
      suc zero + a + a * b + b
   ≡⟨ cong (λ z -> suc zero + z + b) (*-suc-r {a} {b}) ⟩ -- HI con cong
      suc zero + a * suc b + b
   ≡⟨ cong (λ z -> suc zero + z) (+-comm {a * suc b} {b}) ⟩
      suc zero + b + a * suc b
   ≡⟨ cong (λ z -> z + a * suc b) (+-suc-a-is-suc-zero+a {b}) ⟩ -- suc zero + b ≡ b (y un cong)
      suc b + a * suc b
   ≡⟨ refl ⟩ --def de _*_
      suc a * suc b 
   ∎

factor-derecha : {a b c : ℕ} -> (a * b) + a * (b * c) ≡ a * (b + b * c)
factor-derecha {zero} {b} {c} = 
   begin
      (zero * b) + zero * (b * c)
   ≡⟨ *-zero-l {b} ⟩ --doble!
      zero + zero
   ≡⟨ zeroPlus ⟩ 
      zero
   ≡⟨ *-zero-add-v2 {b + b * c} ⟩ 
      zero * (b + b * c)
   ∎
factor-derecha {suc a} {b} {c} =
   begin
      (suc a * b) + suc a * (b * c)
   ≡⟨ refl ⟩
      b + a * b + suc a * (b * c) 
   ≡⟨ cong (λ z -> b + a * b + z) refl ⟩ 
      b + a * b + (b * c + a * (b * c))
   ≡⟨ sym (+-assoc {b + a * b} {b * c} {a * (b * c)}) ⟩
      b + a * b + b * c + a * (b * c)
   --+-comm: a + b ≡ b + a
   -- el objetivo ahora es cambiar el segundo termino por el tercero
   --1. asociamos
   ≡⟨ cong (λ w -> w + a * (b * c)) (+-assoc {b} {a * b} {b * c}) ⟩
      b + (a * b + b * c) + a * (b * c)
   --2. cambiamos el orden
   ≡⟨ cong (λ z -> b + z + a * (b * c)) (+-comm {a * b} {b * c}) ⟩
      b + (b * c + a * b) + a * (b * c)
   --3. desasociamos
   ≡⟨ cong (λ u -> u + a * (b * c)) (sym (+-assoc {b} {b * c} {a * b})) ⟩
      b + b * c + a * b + a * (b * c)
   ≡⟨ +-assoc {b + b * c} {a * b} {a * (b * c)} ⟩ 
      (b + b * c) + (a * b + a * (b * c))
   ≡⟨ cong (λ z -> b + b * c + z) (factor-derecha {a} {b} {c}) ⟩
      (b + b * c) + (a * (b + b * c))
   ≡⟨ sym refl ⟩ 
      suc a * (b + b * c)
   ∎
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
    ≡⟨ sym (*-suc-r {a * b} {c})  ⟩
       (a * b) + (a * b * c)
    ≡⟨ cong (λ z -> (a * b) + z) (*-assoc {a} {b} {c}) ⟩ -- hipotesis inductiva
       (a * b) + a * (b * c)
   ≡⟨ factor-derecha {a} {b} {c} ⟩ 
      a * (b + b * c)
    ≡⟨ cong (λ z -> a * z) (*-suc-r {b} {c}) ⟩ 
       a * (b * suc c)
    ∎

-- A.5) Demostrar que el producto es conmutativo.
-- Sugerencia: demostrar lemas auxiliares que prueben que:
--   a * zero = zero
--   a * suc b = a + a * b
*-comm : {a b : ℕ} → a * b ≡ b * a
*-comm {a} {zero} = *-zero-r {a}
*-comm {a} {suc b} = 
   begin
      a * suc b
   ≡⟨ sym (*-suc-r {a} {b})⟩ 
      a + a * b
   ≡⟨ cong (λ z -> a + z) (*-comm {a} {b}) ⟩
      a + b * a
   ≡⟨ sym refl ⟩ 
      suc b * a
   ∎

-- A.3) Demostrar que el producto distribuye sobre la suma (a izquierda).
-- lo cambie de orden para poder reutilizar otros predicados auxiliares
*-+-distrib-l : {a b c : ℕ} → (a + b) * c ≡ a * c + b * c
*-+-distrib-l {a} {b} {zero} = 
   begin
      (a + b) * zero
   ≡⟨ *-zero-r {a + b}⟩
      zero
   ≡⟨ sym (sumOfZeroProductIsZero {a} {b})⟩
      a * zero + b * zero
   ∎
*-+-distrib-l {a} {b} {suc c} =
   begin
     (a + b) * suc c
   ≡⟨ sym (*-suc-r {a + b} {c}) ⟩
      a + b + ((a + b) * c)
   ≡⟨ cong (λ z -> a + b + z) (*-+-distrib-l {a} {b} {c}) ⟩  
      a + b + (a * c + b * c)
   ≡⟨ sym (+-assoc {a + b} {a * c} {b * c}) ⟩
      a + b + a * c + b * c 
   -- acomodamos todo....
   ≡⟨ cong (λ z -> z + b * c) (+-assoc {a} {b} {a * c}) ⟩
      a + (b + a * c) + b * c
   ≡⟨ cong (λ z -> a + z + b * c) (+-comm {b} {a * c}) ⟩
      a + (a * c + b) + b * c
   ≡⟨ cong (λ z -> z + b * c) (sym (+-assoc {a} {a * c} {b})) ⟩
      a + a * c + b + b * c
   ≡⟨ +-assoc {a + a * c} {b} {b * c} ⟩ 
   -- listo, quedo todo en orden
      a + a * c + (b + b * c)
   ≡⟨ cong (λ z -> z + (b + b * c)) (*-suc-r {a} {c}) ⟩ 
      a * suc c + (b + b * c)
   ≡⟨ cong (λ z -> a * suc c + z) (*-suc-r {b} {c}) ⟩ 
      a * suc c + b * suc c
   ∎


-- A.6) Demostrar que el producto distribuye sobre la suma (a derecha).
-- Sugerencia: usar la conmutatividad y la distributividad a izquierda.
*-+-distrib-r : {a b c : ℕ} → a * (b + c) ≡ a * b + a * c
*-+-distrib-r {zero} {b} {c} = *-zero-l {b + c}
*-+-distrib-r {suc a} {b} {c} = 
   begin
      suc a * (b + c)
   ≡⟨ *-comm {suc a} {b + c} ⟩ 
      (b + c) * suc a
   ≡⟨ *-+-distrib-l {b} {c} {suc a}⟩ 
      b * suc a + c * suc a
   ≡⟨ cong (λ z -> z + c * suc a) (*-comm {b} {suc a}) ⟩ 
      suc a * b + c * suc a
   ≡⟨ cong (λ z -> suc a * b + z) (*-comm {c} {suc a}) ⟩ 
      suc a * b + suc a * c
   ∎

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
zeroPlusRemoved : {a b : ℕ} -> zero + a ≡ b -> a ≡ b
zeroPlusRemoved {zero} {b} zeroPlusZeroIsB = 
   begin
      zero
   ≡⟨ plusZero {zero} ⟩
      zero + zero
   ≡⟨ zeroPlusZeroIsB ⟩
      b 
   ∎
zeroPlusRemoved {suc a} {zero} ()
zeroPlusRemoved {suc a} {suc b} ZeroPlusSucAIsSucB = 
   begin
      suc a
   ≡⟨ zeroPlus ⟩ 
      zero + suc a
   ≡⟨ ZeroPlusSucAIsSucB ⟩ 
      suc b
   ∎


kMasSucNEsSucM : {k n m : ℕ} -> (k + n ≡ m) -> k + suc n ≡ suc m
kMasSucNEsSucM {zero} {n} {m} zeroPlusNIsM = 
   begin
      zero + suc n
   ≡⟨ zeroPlus ⟩
      suc n
   ≡⟨ +-suc-a-is-suc-zero+a ⟩  
      suc zero + n
   ≡⟨ cong (λ z -> suc zero + z) (zeroPlusRemoved zeroPlusNIsM) ⟩ 
      suc zero + m
   ≡⟨ +-suc-a-is-suc-zero+a ⟩  
      suc m
   ∎
kMasSucNEsSucM {suc k} {n} {m} sucKPlusNIsM = 
   begin
      suc k + suc n
   ≡⟨ cong (λ z -> suc k + z) (+-suc-a-is-suc-zero+a {n})⟩
   -- parentesis...
      suc k + (suc zero + n)
   ≡⟨ sym (+-assoc {suc k} {suc zero} {n}) ⟩
      suc k + suc zero + n
   -- ahora si
   ≡⟨ cong (λ z → z + n) (+-comm {suc k} {suc zero}) ⟩
      suc zero + suc k + n
   ≡⟨ cong (λ z -> suc zero + z) (sucKPlusNIsM) ⟩  
      suc zero + m
   ≡⟨ +-suc-a-is-suc-zero+a ⟩ 
      suc m
   ∎


≤?-correcta : {n m : ℕ} → (n ≤? m) ≡ true → n ≤ m
≤?-correcta {zero} {m} _ = m , (sym (plusZero {m}))
-- aca nunca se va a pattern-matchear.
-- dado que no es posible que suc _ ≤? zero sea true
≤?-correcta {suc n} {zero} ()
-- Aca queremos encontrar un par (k, p)
-- Donde k : ℕ, y p, dado un ℕ, devuelve
-- una prueba de que k + suc n ≡ suc m
-- tambien podria usar que suc k + suc m ≡ suc (k + m) por def.
≤?-correcta {suc n} {suc m} dem = 
   -- "p" nos dice que k + n ≡ m
   let k , p = ≤?-correcta {n} {m} dem in (k , kMasSucNEsSucM p)


-- B.2) Demostrar que es imposible que el cero sea el sucesor de algún natural:

zero-no-es-suc : {n : ℕ} → suc n ≡ zero → ⊥
zero-no-es-suc ()

suc≤zero->⊥ : {a : ℕ} -> suc a ≤ zero -> ⊥
suc≤zero->⊥ {a} (k , p) = zero-no-es-suc (trans (sym (suc-comm-inverse {k} {a})) p)

-- B.3) Demostrar que la función es completa con respecto a su especificación.
-- Sugerencia: seguir el esquema de inducción con el que se define la función _≤?_.
-- * Para el caso en el que n = suc n' y m = zero, usar el ítem B.2 y propiedades de la suma.
-- * Para el caso en el que n = suc n' y m = suc m', recurrir a la hipótesis inductiva y propiedades de la suma.

suc-cancel : {a b : ℕ} -> suc a ≡ suc b -> a ≡ b
suc-cancel refl = refl

suc-comm-inverse-receives-equality : {a b k : ℕ} -> k + suc a ≡ suc b -> suc (k + a) ≡ suc b
--gpt...
suc-comm-inverse-receives-equality {a} {b} {k} p = trans (sym (suc-comm-inverse {k} {a})) p

suc-n-≤-suc-m-remove-suc : {n m : ℕ} -> suc n ≤ suc m -> n ≤ m
--p es de tipo k + suc n ≡ suc m
suc-n-≤-suc-m-remove-suc {n} {m} (k , p) = k , (suc-cancel (suc-comm-inverse-receives-equality {n} {m} {k} p))

≤?-completa : {n m : ℕ} → n ≤ m → (n ≤? m) ≡ true
≤?-completa {zero} {zero} (zero , _) = refl 
≤?-completa {suc n} {zero} sucNLessThanZero = ⊥-elim (suc≤zero->⊥ sucNLessThanZero)
--En este caso nos dan que p es "k + n ≤ suc m"
≤?-completa {zero} {suc m} (k , p) = refl
≤?-completa {suc n} {suc m} sucNLeqSucM = ≤?-completa {n} {m} (suc-n-≤-suc-m-remove-suc sucNLeqSucM)
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


suc≤-to-≤ : {m n : ℕ} → suc m ≤ suc n → m ≤ n
suc≤-to-≤ {m} {n} (k , p) =
  k , suc-cancel (trans (sym (suc-comm-inverse {k} {m})) p)

-- C.1) Demostrar el principio de inducción completa, que permite recurrir a la hipótesis
-- inductiva sobre cualquier número estrictamente menor.
ind-completa : (C : ℕ → Set)
               (f : (n : ℕ)
                  → ((m : ℕ) → m < n → C m)
                  → C n)
               (n : ℕ)
               → C n

-- Dado n ≤ 0, producir C n   
-- como nos estan dando un absurdo (la demo de que m < zero), lo "parseamos" para obtener ⊥, y luego lo eliminamos y
-- para obtener "cualquier cosa". En este caso, C m
ind-completa C f zero = f zero (λ m (k , p) -> ⊥-elim (suc≤zero->⊥ (k , p) ))
-- aca (k , p) es suc n ≤ suc m: lo pasamos a n ≤ m
ind-completa C f (suc n) = 
   f 
      (suc n) 
      (λ m sucNIsLessThanSucM  -> {!   !} )

--------------------------------------------------------------------------------

---- Parte D ----

-- D.1) Usando pattern matching, definir el principio de inducción sobre la
-- igualdad:

ind≡ : {A : Set}
       {C : (a b : A) → a ≡ b → Set}
     → ((a : A) → C a a refl)
     → (a b : A) (p : a ≡ b) → C a b p
ind≡ cEq a _ refl = cEq a

-- D.2) Demostrar nuevamente la simetría de la igualdad, usando ind≡:

sym' : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym' {A} {a} {b} aEqb = ind≡ {C = λ a b _ → b ≡ a} (λ _ -> refl) a b aEqb 

-- D.3) Demostrar nuevamente la transitividad de la igualdad, usando ind≡:

trans' : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans' {A} {a} {b} {c} aEqB bEqC = (ind≡ {C = λ a b _ → (b ≡ c → a ≡ c)} (λ z zIsC -> zIsC) a b aEqB) bEqC

-- D.4) Demostrar nuevamente que la igualdad es una congruencia, usando ind≡:

cong' : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong' {A} {B} {a} {b} f aEqB = ind≡ {C = λ a b _ -> f a ≡ f b} (λ z -> refl) a b aEqB