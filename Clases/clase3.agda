module Clases.clase3 where
open import Data.Nat
       using (ℕ; zero; suc)

data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A


-- No podemos definir el tipo "vacio"! Tendriamos que definir algun tipo
-- "Maybe A" que sea None o A
head : { A : Set } -> List A -> A
head []     = {!   !}
head (x :: xs) = x

---
data Vec (A : Set) (n : ℕ) : Set where
    [] : Vec A n -- si le pongo 0 rompe
    _::_ : {n : ℕ} -> A -> Vec A n -> Vec A (suc n)

vec-head : {A : Set} {n : ℕ} -> Vec A (suc n) -> A
vec-head (x :: _) = x
-- esto no tiene otro caso porque la lista vacia nunca va a unificar con esto
-- porque el "n" que recibe es de forma "suc n". vec-head no esta definido para 
-- ese tipo

-- def de _++_

--tip: se puede definir estos como parametros implicitos
variable A B : Set
variable n m : ℕ
-- guarda igual... se pueden ligar en un orden que no querramos...

reverse : Vec A n -> Vec A n
reverse [] = []
reverse (x :: xs) = reverse xs ++ (x :: [])
-- Esto rompe! reverse xs es de tamaño n, y (x :: []) es de tamaño 1.
-- Finalmente obtenemos n+1, pero queriamos 1 + n!! porque Vec A n es de tamaño "suc n"

--Un fix que se le ocurrio a pablo es...
-- id-swap : ℕ -> ℕ
-- id-swap zero = zero
-- id-swap (suc n) = id-swap n + suc zero
-- reverse : Vec A n -> Vec A (id-swap n)
-- Esto funciona! Igual parece traer problemas despues?



transport : {A : Set} (B : A -> Set) {x y : A} (p : x ≡ y)
           -> B x -> B y
    
transport B refl b = b


...
reverse {A} {suc n}(x :: xs) = transport (Vec A) (+-comm n 1) (reverse xs ++ (x :: []))






