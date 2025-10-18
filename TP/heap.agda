open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _+_; _^_; _∸_; _<_)
open import Data.Nat.Properties using (_≤?_; _≟_; ≤-trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

--auxiliares unreleated
absurdo₁ : {a b : ℕ} -> a ≡ b -> a ≡ suc b -> ⊥
absurdo₁ refl ()

zero-no-es-suc : {a : ℕ} -> zero ≡ suc a -> ⊥ 
zero-no-es-suc ()


-- Caso absurdo en siftUp: r ≤ r₁ ∧ r₁ ≤ r₂ ∧ ¬(r ≤ r₂)
-- Por transitividad: r ≤ r₁ ≤ r₂ implica r ≤ r₂, contradicción
absurdo₂ : {r r₁ r₂ : ℕ} -> r ≤ r₁ -> r₁ ≤ r₂ -> ¬ (r ≤ r₂) -> ⊥
absurdo₂ r≤r₁ r₁≤r₂ r₂<r = r₂<r (≤-trans r≤r₁ r₁≤r₂)

-- min heap btw
data AB : Set where
    nil : AB
    bin : AB -> ℕ -> AB -> AB 

-- data _∈_ : ℕ -> Heap -> Set where
--     ∈-raiz  : ∀ {i r d} -> r ∈ bin i r d
--     ∈-left  : ∀ {k i r d} -> k ∈ i -> k ∈ bin i r d
--     ∈-right : ∀ {k i r d} -> k ∈ d -> k ∈ bin i r d

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

-- Para tenerla cerca
-- data HeapValido : Heap -> Set where
--     heap-nil : HeapValido nil
--     heap-bin : ∀ {i r d} -> HeapValido i -> HeapValido d -> 
--                raizMenorQueHijos (bin i r d) ->  
--                HeapValido (bin i r d)
-- data HeapCompleto : AB -> Set where
--     completo-nil : HeapCompleto nil
--     completo-bin : ∀ h -> esCompleto h -> HeapCompleto h
                
                
-- record Heap (a : AB) : Set where
--     field
--         valido   : HeapValido a
--         completo : HeapCompleto a


completo-nil-aux : ∀ {i r} -> esCompleto (bin i r nil) -> height i ≡ 1
completo-nil-aux s = {!   !}


-- La idea aca es demostrar que, dados dos heaps validos i, d,  y un entero r, siftUp los combina para hacer un
-- -- Heap  valido
siftUp-corrige : ∀ {i r d} -> Heap i -> Heap d -> esCompleto (bin i r d) -> Heap (siftUp (bin i r d))
siftUp-corrige {nil} {r} {nil} hi hd comp = record 
  { valido = heap-bin heap-nil heap-nil tt
  ; completo = completo-bin (bin nil r nil) (inj₁ (refl , tt , tt ))
  }

siftUp-corrige {bin i₁ r₁ d₁} {r} {nil} hi hd comp with r ≤? r₁
... | yes r≤r₁ = record 
  { valido   = {!  !} 
  ; completo = ? --completo-bin (bin (bin i₁ r₁ d₁) r nil) (inj₂ (cong suc (completo-nil-aux {i₁} {r₁} ?) , {!   !}  , tt))
  }
... | no  r>r1 = record 
  { valido = {!   !} 
  ; completo = {!   !}
  }

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