open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_)
open import Data.Nat.Properties using (_≤?_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_)


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
raizMenorQueHijos (bin nil r (bin i r₂ d)) = r ≤ r₂
raizMenorQueHijos (bin (bin i₁ r₁ d₁) r (bin i₂ r₂ d₂)) = (r ≤ r₁) × (r ≤ r₂)

-- Tendria que agregar que un Heap esta completo excepto por el nivel mas bajo?
-- Y si el nivel mas bajo no esta completo, tiene que estar lleno de izquierda a derecha
data HeapValido : Heap -> Set where
    heap-nil : HeapValido nil
    heap-bin : ∀ {i r d} -> HeapValido i -> HeapValido d -> 
               raizMenorQueHijos (bin i r d) ->  
               HeapValido (bin i r d)

-- data HeapCompleto : Heap -> Set where
--     completo-nil : HeapCompleto nil
--     completo-bin: ∀ {i r d} -> 
                
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

esCompleto : Heap -> Set
esCompleto nil = {!   !}
esCompleto (bin i r d) = {!   !} -- formula basada en cant. nodos y altura


-- Corrige el heap elevando hacia arriba el elemento insertado. (hasta donde le corresponda estar)
siftUp : Heap -> Heap
siftUp nil = nil
siftUp (bin i r d) = {!   !}


insertar : ℕ -> Heap -> Heap
insertar n nil = bin nil n nil
insertar n (bin i r d) with height i ≤? height d -- Al nuevo elemento lo insertamos en el subarbol mas pequeño
-- Caso insertamos a la izquierda
... | yes p = siftUp (bin (insertar n i) r d)
-- Caso insertamos a la derecha
... | no  p = siftUp (bin i r (insertar n d))
