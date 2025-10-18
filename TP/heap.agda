open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _+_; _^_; _∸_; _<_)
open import Data.Nat.Properties using (_≤?_; _≟_; ≤-trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

--auxiliares unreleated
absurdo₁ : {a b : ℕ} -> a ≡ b -> a ≡ suc b -> ⊥
absurdo₁ refl ()

-- Caso absurdo en siftUp: r ≤ r₁ ∧ r₁ ≤ r₂ ∧ ¬(r ≤ r₂)
-- Por transitividad: r ≤ r₁ ≤ r₂ implica r ≤ r₂, contradicción
absurdo₂ : {r r₁ r₂ : ℕ} -> r ≤ r₁ -> r₁ ≤ r₂ -> ¬ (r ≤ r₂) -> ⊥
absurdo₂ r≤r₁ r₁≤r₂ r₂<r = r₂<r (≤-trans r≤r₁ r₁≤r₂)

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

esPerfecto : Heap -> Set
esPerfecto nil = ⊤
esPerfecto (bin i r d) = size (bin i r d) ≡ (2 ^ (height (bin i r d))) ∸ 1

esPerfecto? : (h : Heap) -> Dec (esPerfecto h)
esPerfecto? nil = yes tt
esPerfecto? (bin i r d) = size (bin i r d) ≟ (2 ^ (height (bin i r d))) ∸ 1

-- Esta definicion de completo toma en cuenta que se llene de izquierda a derecha.
esCompleto : Heap -> Set
esCompleto nil = ⊤
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
                


-- Corrige el heap elevando hacia arriba el elemento insertado. 
-- La corrección es "local". Es decir, no investiga más allá de la raíz actual.
siftUp : Heap -> Heap
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


insertar : ℕ -> Heap -> Heap
insertar n nil = bin nil n nil
insertar n (bin i r d) with esCompleto? i
... | yes p = siftUp (bin i r (insertar n d))
... | no  p = siftUp (bin (insertar n i) r d)


-- insertar-preserva-invariante : ∀ {x h} -> HeapValido