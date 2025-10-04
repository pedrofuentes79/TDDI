
----
---- Práctica 5: Programas correctos por construcción
----

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≟_)
open import Data.Nat.Properties using (≤-step; ≤-refl; ≤-trans; +-monoʳ-≤)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (subst)

-- Recordemos la definición de algunas funciones básicas sobre listas:

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : {A : Set} → List A → ℕ
length []       = zero
length (_ ∷ xs) = suc (length xs)

reverse : {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

≤-0-is-eq-0 : {k : ℕ} -> (k ≤ zero) -> (k ≡ zero)
≤-0-is-eq-0 {zero} k≤zero = refl

suc-≤-lema : {n m : ℕ} -> suc n ≤ suc m -> n ≤ m
suc-≤-lema {n} {m} (_≤_.s≤s k) = k

---- Parte A ----

-- A.1) Demostrar que dada una lista xs y un entero k ≤ length xs,
-- es posible partir la lista xs en un prefijo ys de longitud k
-- seguido de un sufijo zs.

split : {A : Set} (xs : List A) (k : ℕ)
      → k ≤ length xs
      → Σ[ ys ∈ List A ] Σ[ zs ∈ List A ] ((xs ≡ ys ++ zs) × k ≡ length ys)
split [] k k≤0 = ( [] , [] , refl , ≤-0-is-eq-0 k≤0)
-- k ≤ suc (length xs)
-- qvq k ≡ (length x ∷ [])
-- split (x ∷ xs) k k≤xs+1 = ( x ∷ [] , xs , refl , {!   !} )

split (x ∷ xs) zero k≤xs+1 = ( [] , x ∷ xs , refl , refl)
split {A} (x ∷ xs) (suc k) k+1≤xs+1 with split xs k (suc-≤-lema k+1≤xs+1)
... | (ys , zs , xs≡ys++zs , k≡ys) = ( x ∷ ys , zs , cong (x ∷_) xs≡ys++zs , cong suc k≡ys)
-- 
-- Definimos un predicado "x ∈ ys" que es verdadero si x aparece en ys:

data _∈_ : ℕ → List ℕ → Set where
  zero : {x : ℕ} {xs : List ℕ} → x ∈ (x ∷ xs)
  suc  : {x y : ℕ} {xs : List ℕ} → x ∈ xs → x ∈ (y ∷ xs)

no-number-is-in-[] : {x : ℕ} -> x ∈ [] -> ⊥
no-number-is-in-[] ()

-- TODO: simplificar esto? es medio feo
no-list-with-one-element-is-[]-1 : {A : Set} {x : A} {xs : List A} -> x ∷ xs ≡ [] -> ⊥
no-list-with-one-element-is-[]-1 ()

no-list-with-one-element-is-[]-2 : {A : Set} {x : A} {xs : List A} -> [] ≡ x ∷ xs -> ⊥
no-list-with-one-element-is-[]-2 ()

x-∉-y∷ys : {x y : ℕ} {ys : List ℕ} -> ¬ (x ≡ y) -> ¬ (x ∈ ys) -> (x ∈ (y ∷ ys)) -> ⊥
x-∉-y∷ys x≠y x∉ys zero       = x≠y refl
x-∉-y∷ys x≠y x∉ys (suc x∈ys) = x∉ys x∈ys

-- A.2) Demostrar que es posible decidir si un número natural aparece en una lista.
-- (Usar _≟_ para decidir la igualdad de números naturales).

∈-decidible : {x : ℕ} {ys : List ℕ} → Dec (x ∈ ys)
∈-decidible {x} {[]} = no (no-number-is-in-[])
∈-decidible {x} {y ∷ ys} with x ≟ y
... | yes x≡y = yes (subst (_∈ (y ∷ ys)) (sym x≡y) (zero {y} {ys}))
... | no x!≡y with ∈-decidible {x} {ys}
... | yes x∈ys = yes (suc x∈ys)
... | no x∉ys  = no (x-∉-y∷ys x!≡y x∉ys)

-- A.3) Demostrar que la igualdad de listas es decidible
-- asumiendo que es decidible la igualdad de sus elementos.

list-eq-∷ : {A : Set} {x y : A} {xs ys : List A} -> x ≡ y -> xs ≡ ys -> x ∷ xs ≡ y ∷ ys
list-eq-∷ refl refl = refl

List-igualdad-decidible : {A : Set}
                        → ((x y : A) → Dec (x ≡ y))
                        → ((xs ys : List A) → Dec (xs ≡ ys))
List-igualdad-decidible dec-eq-A [] []             = yes refl
List-igualdad-decidible dec-eq-A (x ∷ xs) []       = no no-list-with-one-element-is-[]-1
List-igualdad-decidible dec-eq-A [] (y ∷ ys)       = no no-list-with-one-element-is-[]-2
List-igualdad-decidible dec-eq-A (x ∷ xs) (y ∷ ys) with dec-eq-A x y
... | no x≠y  = no (λ {refl -> x≠y refl})
... | yes x≡y with List-igualdad-decidible dec-eq-A xs ys
... | yes xs≡ys = yes (list-eq-∷ x≡y xs≡ys)
... | no  xs≠ys = no (λ {refl -> xs≠ys refl})

---- Parte B ----

infix  3 _~_
infix  3 _<<_
infixr 3 _~⟨_⟩_
infix  4 _~∎

-- Considerar el siguiente tipo de las permutaciones:

data _~_ : List ℕ → List ℕ → Set where
  ~-empty : [] ~ []
  ~-cons  : {x : ℕ} {xs ys : List ℕ}
          → xs ~ ys
          → x ∷ xs ~ x ∷ ys
  ~-swap  : {x y : ℕ} {xs ys : List ℕ}
          → xs ~ ys
          → x ∷ y ∷ xs ~ y ∷ x ∷ ys
  ~-trans : {xs ys zs : List ℕ}
          → xs ~ ys
          → ys ~ zs
          → xs ~ zs

-- B.1) Demostrar que "~" es reflexiva:

~-refl : {xs : List ℕ} → xs ~ xs
~-refl {[]} = ~-empty
~-refl {x ∷ xs} = ~-cons ~-refl

-- Definimos operadores auxiliares para poder hacer razonamiento ecuacional
-- con permutaciones:

_~⟨_⟩_ : (xs : List ℕ)
       → {ys : List ℕ} → xs ~ ys
       → {zs : List ℕ} → ys ~ zs
       → xs ~ zs
_ ~⟨ p ⟩ q = ~-trans p q

_~∎ : (xs : List ℕ) → xs ~ xs
_ ~∎ = ~-refl

-- B.2) Demostrar que "~" es simétrica:

~-sym : {xs ys : List ℕ} → xs ~ ys → ys ~ xs
~-sym ~-empty       = ~-empty
~-sym (~-cons p)    = ~-cons (~-sym p)
~-sym (~-swap p)    = ~-swap (~-sym p)
~-sym (~-trans p q) = ~-trans (~-sym q) (~-sym p)

-- B.3) Demostrar que "~" es una congruencia con respecto a la concatenación de listas:

~-++ : {xs ys xs' ys' : List ℕ}
     → xs ~ xs'
     → ys ~ ys'
     → xs ++ ys ~ xs' ++ ys'
~-++ (~-empty) q = q
~-++ (~-cons p) q = ~-cons (~-++ p q) 
~-++ (~-swap p) q = ~-swap (~-++ p q)
~-++ (~-trans p p₁) q = ~-trans (~-++ p q) (~-++ p₁ ~-refl)


-- B.4) Demostrar que una lista invertida es permutación de la lista original:

~-reverse : {xs : List ℕ} → reverse xs ~ xs
~-reverse {[]}     = ~-empty
~-reverse {x ∷ xs} =
    reverse (x ∷ xs)
  ~⟨ ~-refl ⟩
    reverse xs ++ (x ∷ [])
  ~⟨ {!!} ⟩
    xs ++ (x ∷ [])
  ~⟨ {!!} ⟩
    x ∷ xs
  ~∎

----

-- Definimos una función que vale 1 si dos números son iguales, y 0 si no.
iguales? : ℕ → ℕ → ℕ
iguales? x y with x ≟ y
... | yes _ = 1
... | no  _ = 0

-- Definimos una función que cuenta el número de apariciones de un
-- número natural en una lista.
cantidad-apariciones : ℕ → List ℕ → ℕ
cantidad-apariciones x []       = zero
cantidad-apariciones x (y ∷ ys) = iguales? x y + cantidad-apariciones x ys

-- Definimos un predicado xs << ys
-- que es verdadero si cada natural z
-- aparece en xs a lo sumo tantas veces como aparece en ys:

_<<_ : List ℕ → List ℕ → Set
xs << ys = (z : ℕ) → cantidad-apariciones z xs ≤ cantidad-apariciones z ys

-- B.5) Demostrar las siguientes propiedades de "<<":

<<-empty : [] << []
<<-empty = {!!}

<<-refl : {xs : List ℕ} → xs << xs
<<-refl z = {!!}    -- útil: Data.Nat.Properties.≤-refl 

<<-cons : {x : ℕ} {xs ys : List ℕ} → xs << ys → x ∷ xs << x ∷ ys
<<-cons {x} xs<<ys z = {!!}    -- útil:   +-monoʳ-≤ (iguales? z x) ?

<<-swap : {x y : ℕ} {xs ys : List ℕ} → xs << ys → x ∷ y ∷ xs << y ∷ x ∷ ys
<<-swap xs<<ys z = {!!}    -- útil: Data.Nat.Properties.+-monoʳ-≤

<<-trans : {xs ys zs : List ℕ} → xs << ys → ys << zs → xs << zs
<<-trans xs<<ys ys<<zs z = {!!}    -- útil: Data.Nat.Properties.≤-trans

-- B.6) Usando los lemas de B.5, demostrar que la relación "~" es
-- correcta con respecto a "<<".

~-correcta : {xs ys : List ℕ}
           → xs ~ ys 
           → xs << ys 
~-correcta ~-empty       = {!!}
~-correcta (~-cons p)    = {!!}
~-correcta (~-swap p)    = {!!}
~-correcta (~-trans p q) = {!!}
