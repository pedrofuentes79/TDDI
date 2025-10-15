open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _+_; _^_; _∸_)
open import Data.Nat.Properties using (_≤?_; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

--auxiliares unreleated
absurdo₁ : {a b : ℕ} -> a ≡ b -> a ≡ suc b -> ⊥
absurdo₁ refl ()

-- min heap btw
data Heap : Set where
    nil : Heap
    bin : Heap -> ℕ -> Heap -> Heap

data _∈_ : ℕ -> Heap -> Set where
    ∈-raiz  : ∀ {i r d} -> r ∈ bin i r d
    ∈-left  : ∀ {k i r d} -> k ∈ i -> k ∈ bin i r d
    ∈-right : ∀ {k i r d} -> k ∈ d -> k ∈ bin i r d

-- Verifica que la raíz de un heap sea menor o igual que sus hijos directos
-- Queda simple si separamos en casos.
raizMenorQueHijos : Heap -> Set
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

height : Heap -> ℕ
height nil = zero
height (bin i r d) = suc (height i ⊔ height d)

size : Heap -> ℕ
size nil = 0
size (bin i r d) = 1 + size i + size d

estaVacio : Heap -> Set
estaVacio nil = ⊤
estaVacio (bin i r d) = ⊥

estaVacio? : (h : Heap) -> Dec (estaVacio h)
estaVacio? nil = yes tt
estaVacio? (bin i r d) = no (λ ())

esPerfecto : Heap -> Set
esPerfecto nil = ⊤
esPerfecto (bin i r d) = size (bin i r d) ≡ (2 ^ (height (bin i r d))) ∸ 1

esPerfecto? : (h : Heap) -> Dec (esPerfecto h)
esPerfecto? nil = yes tt
esPerfecto? (bin i r d) = size (bin i r d) ≟ (2 ^ (height (bin i r d))) ∸ 1

-- Esta definicion de completo toma en cuenta que se llene de izquierda a derecha.
esCompleto : Heap -> Set
esCompleto nil = ⊤
-- esCompleto (bin i r d) with height i ≟ height d
-- -- Caso de que tienen la misma altura. Necesito que el de la izquierda sea perfecto (este todo lleno el nivel inferior)
-- -- Y que el derecho le queden algunos por llenar (completo)
-- ... | yes i≡d = esPerfecto i × esCompleto d 
-- ... | no  _ with height i ≟ suc (height d)
-- -- Caso de que el de la derecha es UNO mas bajito que el de la izquierda. 
-- -- Esto nos dice que el de la izquierda aun no se lleno. 
-- -- Por lo tanto, tenemos que pedir que el de la derecha sea perfecto (si no, hubiese estado mal empezar a llenar a la izq)
-- -- Y que el de la izquierda este completo
-- ... | yes i≡d+1 = esCompleto i × esPerfecto d 
-- -- Este caso no entra en ninguno de los establecidos. Por lo tanto, no es completo
-- ... | no  _ = ⊥
esCompleto (bin i r d) = 
  (height i ≡ height d × esPerfecto i × esCompleto d) ⊎ 
  (height i ≡ suc (height d) × esCompleto i × esPerfecto d)

esCompleto? : (h : Heap) -> Dec (esCompleto h)
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

data HeapValido : Heap -> Set where
    heap-nil : HeapValido nil
    heap-bin : ∀ {i r d} -> HeapValido i -> HeapValido d -> 
               raizMenorQueHijos (bin i r d) ->  
               HeapValido (bin i r d)

data HeapCompleto : Heap -> Set where
    completo-nil : HeapCompleto nil
    completo-bin : ∀ h -> esCompleto h -> HeapCompleto h
                

-- Corrige el heap elevando hacia arriba el elemento insertado. (hasta donde le corresponda estar)
siftUp : Heap -> Heap
siftUp nil = nil
siftUp (bin i r d) = {!   !}


insertar : ℕ -> Heap -> Heap
insertar n nil = bin nil n nil
insertar n (bin i r d) with esCompleto? i
... | yes p = siftUp (bin i r (insertar n d))
... | no  p = siftUp (bin (insertar n i) r d)