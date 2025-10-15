open import Data.Nat using (ℕ; zero; suc; _≤_)
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

raizMenorQue : ℕ -> Heap -> Set
raizMenorQue n nil = ⊤
raizMenorQue n (bin i r d) = (n ≤ r) × raizMenorQue n i × raizMenorQue n d

data HeapValido : Heap -> Set where
    heap-nil : HeapValido nil
    heap-bin : ∀ {i r d} -> HeapValido i -> HeapValido d -> 
               raizMenorQue r i -> raizMenorQue r d ->  
               HeapValido (bin i r d)
                
-- queda definir "extraerMax" (que viene de la mano con siftDown)
-- y definir insertar (que usa siftUp)
-- Propiedades
-- siftDown-corrige
-- siftUp-corrige
-- insertar-preserva-heap
-- extraer-max-preserva-heap

insertar : ℕ -> Heap -> Heap
insertar n nil = bin nil n nil
insertar n (bin i r d) = {!   !}