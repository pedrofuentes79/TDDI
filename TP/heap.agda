open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _+_; _^_; _∸_; _<_; _>_)
open import Data.Nat.Properties using (_≤?_; _≟_; ≤-trans; ≤-total)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)


--auxiliares unreleated
absurdo₁ : {a b : ℕ} -> a ≡ b -> a ≡ suc b -> ⊥
absurdo₁ refl ()

zero-no-es-suc : {a : ℕ} -> zero ≡ suc a -> ⊥ 
zero-no-es-suc ()

>-es-≤ : {a b : ℕ} -> (a ≤ b -> ⊥) -> b ≤ a
>-es-≤ {a} {b} a>b with ≤-total a b
... | inj₁ a≤b = ⊥-elim (a>b a≤b)
... | inj₂ b≤a = b≤a

-- Caso absurdo en siftUp: r ≤ r₁ ∧ r₁ ≤ r₂ ∧ ¬(r ≤ r₂)
-- Por transitividad: r ≤ r₁ ≤ r₂ implica r ≤ r₂, contradicción
absurdo₂ : {r r₁ r₂ : ℕ} -> r ≤ r₁ -> r₁ ≤ r₂ -> ¬ (r ≤ r₂) -> ⊥
absurdo₂ r≤r₁ r₁≤r₂ r₂<r = r₂<r (≤-trans r≤r₁ r₁≤r₂)

-- min heap btw
data AB : Set where
    nil : AB
    bin : AB -> ℕ -> AB -> AB 

-- Verifica que la raíz de un heap sea menor o igual que sus hijos directos
-- Queda simple si separamos en casos.
raizMenorQueHijos : AB -> Set
raizMenorQueHijos nil = ⊤
raizMenorQueHijos (bin nil r nil) = ⊤
raizMenorQueHijos (bin (bin i r₁ d) r nil) = r ≤ r₁
raizMenorQueHijos (bin nil r (bin i r₁ d)) = r ≤ r₁
raizMenorQueHijos (bin (bin i₁ r₁ d₁) r (bin i₂ r₂ d₂)) = (r ≤ r₁) × (r ≤ r₂)

-- queda definir "extraerMax" (que viene de la mano con siftDown)
-- y definir insertar (que usa siftUp)
-- Propiedades
-- siftDown-corrige
-- siftUp-corrige
-- insertar-preserva-heap
-- extraer-max-preserva-heap

height : AB -> ℕ
height nil = zero
height (bin i r d) = suc (height i ⊔ height d)

size : AB -> ℕ
size nil = 0
size (bin i r d) = 1 + size i + size d

-- un heap es perfecto si todos sus niveles estan llenos (incluso el de abajo)
esPerfecto : AB -> Set
esPerfecto nil = ⊤
esPerfecto (bin i r d) = size (bin i r d) ≡ (2 ^ (height (bin i r d))) ∸ 1

esPerfecto? : (h : AB) -> Dec (esPerfecto h)
esPerfecto? nil = yes tt
esPerfecto? (bin i r d) = size (bin i r d) ≟ (2 ^ (height (bin i r d))) ∸ 1

-- Esta definicion de completo toma en cuenta que se llene de izquierda a derecha.
esCompleto : AB -> Set
esCompleto nil = ⊤
esCompleto (bin i r d) = 
  (height i ≡ height d       × esPerfecto i × esCompleto d) ⊎ 
  (height i ≡ suc (height d) × esCompleto i × esPerfecto d)

esCompleto? : (h : AB) -> Dec (esCompleto h)
esCompleto? nil = yes tt 
-- Esto es realmente asqueroso. Pido disculpas. Pero no le pude encontrar la vuelta de sintaxis para escribirlo bien
esCompleto? (bin i r d) with height i ≟ height d | esPerfecto? i | esCompleto? d | height i ≟ suc (height d) | esCompleto? i | esPerfecto? d
-- Caso: misma altura, i perfecto, d completo
... | yes eq | yes iperf | yes dcomp | _       | _         | _         = yes (inj₁ (eq , iperf , dcomp))
-- Caso: misma altura, i no perfecto
... | yes eq | no ¬iperf | _         | _       | _         | _         = no λ { (inj₁ (_ , iperf , _)) -> ¬iperf iperf ; (inj₂ (eq' , _ , _)) -> absurdo₁ eq eq' }
-- Caso: misma altura, d no completo
... | yes eq | _         | no ¬dcomp | _       | _         | _         = no λ { (inj₁ (_ , _ , dcomp)) -> ¬dcomp dcomp ; (inj₂ (eq' , _ , _)) -> absurdo₁ eq eq' }
-- Caso: distinta altura pero la correcta, i completo, d perfecto
... | no ¬eq | _         | _         | yes eq' | yes icomp | yes dperf = yes (inj₂ (eq' , icomp , dperf)) 
-- Caso: distinta altura pero la correcta, i no completo
... | no ¬eq | _         | _         | yes eq' | no ¬icomp | _         = no λ { (inj₁ (eq , _ , _)) -> ¬eq eq ; (inj₂ (_ , icomp , _)) -> ¬icomp icomp }
-- Caso: distinta altura pero la correcta, d no perfecto
... | no ¬eq | _         | _         | yes eq' | _         | no ¬dperf = no λ { (inj₁ (eq , _ , _)) -> ¬eq eq ; (inj₂ (_ , _ , dperf)) -> ¬dperf dperf }
-- Caso: alturas incorrectas
... | no ¬eq | _         | _         | no ¬eq' | _         | _         = no λ { (inj₁ (eq , _ , _)) -> ¬eq eq ; (inj₂ (eq' , _ , _)) -> ¬eq' eq' }

esNil : (h : AB) -> Set
esNil nil = ⊤
esNil (bin i r d) = ⊥

esNil? : (h : AB) -> Dec (esNil h)
esNil? nil = yes tt
esNil? (bin i r d) = no λ { () }


data HeapValido : AB -> Set where
    heap-nil : HeapValido nil
    heap-bin : ∀ {i r d} -> HeapValido i -> HeapValido d -> 
               raizMenorQueHijos (bin i r d) ->  
               HeapValido (bin i r d)

data HeapCompleto : AB -> Set where
    completo-nil : HeapCompleto nil
    completo-bin : ∀ h -> esCompleto h -> HeapCompleto h
                
record Heap (a : AB) : Set where
    field
        valido   : HeapValido a
        completo : HeapCompleto a



-- Corrige el heap elevando hacia arriba el elemento insertado. 
-- La corrección es "local". Es decir, no investiga más allá de la raíz actual.
siftUp : AB -> AB
siftUp nil = nil
siftUp (bin nil r nil) = bin nil r nil
siftUp (bin nil r (bin i₁ r₁ d₁)) with r ≤? r₁
... | yes p = bin nil r  (bin i₁ r₁ d₁)
... | no p  = bin nil r₁ (bin i₁ r  d₁)
siftUp (bin (bin i₁ r₁ d₁) r nil) with r ≤? r₁
... | yes p = bin (bin i₁ r₁ d₁) r nil
... | no  p = bin (bin i₁ r d₁) r₁ nil
siftUp (bin (bin i₁ r₁ d₁) r (bin i₂ r₂ d₂)) with r ≤? r₁ | r ≤? r₂ | r₁ ≤? r₂
-- r es el mínimo
... | yes r≤r₁ | yes r≤r₂ | _         = bin (bin i₁ r₁ d₁) r (bin i₂ r₂ d₂)
-- ABSURDO (r ≤ r₁ ∧ r₂ < r ∧ r₁ ≤ r₂ → r₁ ≤ r₂ < r ≤ r₁)
... | yes r≤r₁ | no  r₂<r  | yes r₁≤r₂ = ⊥-elim (absurdo₂ r≤r₁ r₁≤r₂ r₂<r)
-- r₂ es el mínimo (r₂ < r ∧ r₂ < r₁)
... | yes r≤r₁ | no  r₂<r | no  r₂<r₁ = bin (bin i₁ r₁ d₁) r₂ (bin i₂ r d₂)
-- r₁ es el mínimo (r₁ < r ≤ r₂ ∧ r₁ ≤ r₂)
... | no  r₁<r | yes r≤r₂ | yes r₁≤r₂ = bin (bin i₁ r d₁) r₁ (bin i₂ r₂ d₂)
-- r es el mínimo (r < r₁, r ≤ r₂ < r₁ → r ≤ r₂ < r₁)
... | no  r₁<r | yes r≤r₂ | no  r₂<r₁ = bin (bin i₁ r₁ d₁) r (bin i₂ r₂ d₂)
-- r₁ es el mínimo (r₁ < r ∧ r₂ < r ∧ r₁ ≤ r₂)
... | no  r₁<r | no  r₂<r | yes r₁≤r₂ = bin (bin i₁ r d₁) r₁ (bin i₂ r₂ d₂)
-- r₂ es el mínimo (r₁ < r ∧ r₂ < r ∧ r₂ < r₁)
... | no  r₁<r | no  r₂<r | no  r₂<r₁ = bin (bin i₁ r₁ d₁) r₂ (bin i₂ r d₂)


insertar : ℕ -> AB -> AB
insertar n nil = bin nil n nil
insertar n (bin i r d) with esCompleto? i
... | yes p = siftUp (bin i r (insertar n d))
... | no  p = siftUp (bin (insertar n i) r d)


es-nil-es-valido : ∀ {i} -> esNil i -> HeapValido i
es-nil-es-valido {nil} esnil = heap-nil
es-nil-es-valido {bin i r d} ()

raiz-es-menor-que-nil : ∀ {i r d} -> esNil i -> esNil d -> raizMenorQueHijos (bin i r d)
raiz-es-menor-que-nil {nil} {_} {nil} inil dnil = tt
raiz-es-menor-que-nil {bin i₁ r₁ d₁} () 

-- Esto nos dice que, si i es un bin (no nil) y bin i r nil es completo, entonces i tiene altura 1
completo-bin-nil-aux : ∀ {i₁ r₁ d₁ r} -> esCompleto (bin (bin i₁ r₁ d₁) r nil) -> height (bin i₁ r₁ d₁) ≡ 1
completo-bin-nil-aux {i₁} {r₁} {d₁} {r} (inj₁ (() , _ , _)) -- no puede pasar...
completo-bin-nil-aux {i₁} {r₁} {d₁} {r} (inj₂ (hi≡suc_heightnil , _ , _)) = hi≡suc_heightnil

-- Extrae esCompleto del hijo izquierdo cuando el derecho es nil
-- en particular, i₁ y d₁ deben ser nil tambien
extraer-completo-izq : ∀ {i₁ r₁ d₁ r} -> esCompleto (bin (bin i₁ r₁ d₁) r nil) -> esCompleto (bin i₁ r₁ d₁)
extraer-completo-izq (inj₁ (() , _ , _))
extraer-completo-izq (inj₂ (_ , inj₁ (hi≡hd , iperf , dcomp) , _)) = inj₁ (hi≡hd , iperf , dcomp)
extraer-completo-izq (inj₂ (_ , inj₂ (hi≡suchd , icomp , dperf) , _)) = inj₂ (hi≡suchd , icomp , dperf)

-- Auxiliares para extraer que los hijos son nil
hijo-izq-nil-de-altura-1 : ∀ {i r d} -> height (bin i r d) ≡ 1 -> esNil i
hijo-izq-nil-de-altura-1 {nil} {r} {nil} refl = tt
hijo-izq-nil-de-altura-1 {nil} {r} {bin i₂ r₂ d₂} ()
hijo-izq-nil-de-altura-1 {bin i₁ r₁ d₁} {r} {nil} ()
hijo-izq-nil-de-altura-1 {bin i₁ r₁ d₁} {r} {bin i₂ r₂ d₂} ()

hijo-der-nil-de-altura-1 : ∀ {i r d} -> height (bin i r d) ≡ 1 -> esNil d
hijo-der-nil-de-altura-1 {nil} {r} {nil} refl = tt
hijo-der-nil-de-altura-1 {nil} {r} {bin i₂ r₂ d₂} ()
hijo-der-nil-de-altura-1 {bin i₁ r₁ d₁} {r} {nil} ()
hijo-der-nil-de-altura-1 {bin i₁ r₁ d₁} {r} {bin i₂ r₂ d₂} ()

-- La idea aca es demostrar que, dados dos heaps validos i, d,  y un entero r, siftUp los combina para hacer un
-- -- Heap  valido
siftUp-corrige : ∀ {i r d} -> Heap i -> Heap d -> esCompleto (bin i r d) -> Heap (siftUp (bin i r d))
-- CASO IZQ Y DER NULOS
siftUp-corrige {nil} {r} {nil} hi hd comp = record 
  { valido = heap-bin heap-nil heap-nil tt
  ; completo = completo-bin (bin nil r nil) (inj₁ (refl , tt , tt ))
  }

-- CASO EL DE LA IZQUIERDA NO ES NULO
siftUp-corrige {bin i₁ r₁ d₁} {r} {nil} hi hd comp with r ≤? r₁ | esNil? i₁ | esNil? d₁
... | yes r≤r₁ | yes i₁nil | yes d₁nil   = record 
  { valido   = heap-bin (heap-bin (es-nil-es-valido i₁nil) (es-nil-es-valido d₁nil) (raiz-es-menor-que-nil i₁nil d₁nil)) 
                        heap-nil 
                        r≤r₁
  ; completo = completo-bin (bin (bin i₁ r₁ d₁) r nil) (inj₂ (completo-bin-nil-aux {i₁} {r₁} {d₁} {r} comp , extraer-completo-izq {i₁} {r₁} {d₁} {r} comp , tt))
  }
... | no  r>r₁ | yes i₁nil | yes d₁nil = record 
  { valido = heap-bin (heap-bin (es-nil-es-valido i₁nil) (es-nil-es-valido d₁nil) (raiz-es-menor-que-nil i₁nil d₁nil))
             heap-nil 
             (>-es-≤ r>r₁)
  ; completo = completo-bin (bin (bin i₁ r d₁) r₁ nil) (inj₂ (completo-bin-nil-aux {i₁} {r} {d₁} {r₁} comp , extraer-completo-izq {i₁} {r} {d₁} {r} comp , tt))
  }
-- Estos casos son imposibles: dado que es completo, el arbol de la izquierda solo puede tener un nodo
-- Esos holes los deberia llenar llegando a que esNil i₁ se desprende de hi + comp
... | _ | no i₁notnil | _  = ⊥-elim (i₁notnil (hijo-izq-nil-de-altura-1 {i₁} {r₁} {d₁} (completo-bin-nil-aux {i₁} {r₁} {d₁} {r} comp )))
... | _ | _  | no d₁notnil = ⊥-elim (d₁notnil (hijo-der-nil-de-altura-1 {i₁} {r₁} {d₁} (completo-bin-nil-aux {i₁} {r₁} {d₁} {r} comp )))

-- CASO EL DE LA DERECHA NO ES NULO
-- Este caso deberia ser imposible
siftUp-corrige {nil} {r} {bin nil r₂ nil} hi hd (inj₁ (zero≡suc , _ , _ )) = ⊥-elim (zero-no-es-suc zero≡suc)
siftUp-corrige {nil} {r} {bin nil r₂ nil} hi hd (inj₂ (zero≡suc , _ , _ )) = ⊥-elim (zero-no-es-suc zero≡suc)

-- Caso general
siftUp-corrige {bin i₁ r₁ d₁} {r} {bin i₂ r₂ d₂} hi hd comp = record 
  { valido = {!   !} 
  ; completo = {!   !} 
  }

insertar-preserva-invariante : ∀ {h n} -> Heap h -> Heap (insertar n h)
insertar-preserva-invariante {nil} {n} k = record
  { valido = {!   !} 
  ; completo = {!   !} 
  }
insertar-preserva-invariante {bin i r d} {n} k = record
  { valido = {!   !} 
  ; completo = {!   !} 
  }
