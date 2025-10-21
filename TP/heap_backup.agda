open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _+_; _∸_; _<_; _>_; s≤s; z≤n)
open import Data.Nat.Properties using (_≤?_; _≟_; ≤-trans; ≤-total; ⊔-idem; ⊔-comm; m≤n⇒m⊔n≡n; ⊔-identityʳ; n≤1+n)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

--auxiliares 
absurdo₁ : {a b : ℕ} -> a ≡ b -> a ≡ suc b -> ⊥
absurdo₁ refl ()

zero-no-es-suc : {a : ℕ} -> zero ≡ suc a -> ⊥ 
zero-no-es-suc ()

>-es-≤ : {a b : ℕ} -> (a ≤ b -> ⊥) -> b ≤ a
>-es-≤ {a} {b} a>b with ≤-total a b
... | inj₁ a≤b = ⊥-elim (a>b a≤b)
... | inj₂ b≤a = b≤a

<-es-≤ : {a b : ℕ} -> (b ≤ a -> ⊥) -> a ≤ b
<-es-≤ {a} {b} a<b with ≤-total a b
... | inj₁ a≤b = a≤b
... | inj₂ b≤a = ⊥-elim (a<b b≤a)

-- Caso absurdo en siftUp: r ≤ r₁ ∧ r₁ ≤ r₂ ∧ ¬(r ≤ r₂)
-- Por transitividad: r ≤ r₁ ≤ r₂ implica r ≤ r₂, contradicción
absurdo₂ : {r r₁ r₂ : ℕ} -> r ≤ r₁ -> r₁ ≤ r₂ -> ¬ (r ≤ r₂) -> ⊥
absurdo₂ r≤r₁ r₁≤r₂ r₂<r = r₂<r (≤-trans r≤r₁ r₁≤r₂)

-- definimos una estructura base de arbol binario
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

-- queda definir "extraerMax" (que viene de la mano con siftDown?)
-- Propiedades
-- siftDown-corrige
-- extraer-max-preserva-heap

raizDe : AB -> ℕ
raizDe nil           = 0
raizDe (bin _ r _) = r

setRaiz : AB -> ℕ -> AB
setRaiz nil           n = bin nil n nil
setRaiz (bin i _ d) n = bin i n d

height : AB -> ℕ
height nil = zero
height (bin i r d) = suc (height i ⊔ height d)

size : AB -> ℕ
size nil = 0
size (bin i r d) = 1 + size i + size d

-- un árbol es perfecto si ambos subárboles tienen la misma altura y son perfectos
esPerfecto : AB -> Set
esPerfecto nil = ⊤
esPerfecto (bin i r d) = height i ≡ height d × esPerfecto i × esPerfecto d

esPerfecto? : (h : AB) -> Dec (esPerfecto h)
esPerfecto? nil = yes tt
esPerfecto? (bin i r d) with height i ≟ height d | esPerfecto? i | esPerfecto? d
... | yes hi≡hd  | yes iperf | yes dperf = yes (hi≡hd , iperf , dperf)
... | no  ¬hi≡hd | _         | _         = no λ { (hi≡hd , _ , _) → ¬hi≡hd hi≡hd }
... | _          | no ¬iperf | _         = no λ { (_ , iperf , _) → ¬iperf iperf }
... | _          | _         | no ¬dperf = no λ { (_ , _ , dperf) → ¬dperf dperf }

-- Esta definicion de completo toma en cuenta que se llene de izquierda a derecha.
-- todo: definir esCompleto en base a "tiene estructura de heap de n nodos" 
esCompleto : AB -> Set
esCompleto nil = ⊤
esCompleto (bin i r d) = 
  (height i ≡ height d       × esPerfecto i × esCompleto d) 
  ⊎ 
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

perfecto-implica-completo : ∀ {a} -> esPerfecto a -> esCompleto a
perfecto-implica-completo {nil} perf = tt
perfecto-implica-completo {bin i r d} (hi≡hd , iperf , dperf) = inj₁ (hi≡hd , iperf , perfecto-implica-completo dperf) 

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
                
-- esHeap
record Heap (a : AB) : Set where
    field
        valido   : HeapValido a
        completo : HeapCompleto a

heap-valido-su-hijo-izq-es-valido : ∀ {i r d} -> HeapValido (bin i r d) -> HeapValido i
heap-valido-su-hijo-izq-es-valido (heap-bin ival _ _ ) = ival

heap-valido-su-hijo-der-es-valido : ∀ {i r d} -> HeapValido (bin i r d) -> HeapValido d
heap-valido-su-hijo-der-es-valido (heap-bin _ dval _) = dval

heap-valido-con-raiz-aun-menor-es-valido : ∀ {i r d r₁} -> HeapValido (bin i r d) -> r₁ ≤ r -> raizMenorQueHijos (bin i r₁ d)
heap-valido-con-raiz-aun-menor-es-valido {nil} {r} {nil} {r₁} (heap-bin ival dval rmqh) r₁≤r                = tt
heap-valido-con-raiz-aun-menor-es-valido {nil} {r} {bin i₃ r₃ d₃} {r₁} (heap-bin ival dval rmqh) r₁≤r       = (≤-trans r₁≤r rmqh)
heap-valido-con-raiz-aun-menor-es-valido {bin i₂ r₂ d₂} {r} {nil} {r₁} (heap-bin ival dval rmqh) r₁≤r       = (≤-trans r₁≤r rmqh)
heap-valido-con-raiz-aun-menor-es-valido {bin i₂ r₂ d₂} {r} {bin i₃ r₃ d₃} {r₁} (heap-bin ival dval (r≤r₂ , r≤r₃)) r₁≤r = (≤-trans r₁≤r r≤r₂ , ≤-trans r₁≤r r≤r₃)

extraer-esCompleto : ∀ {h} -> HeapCompleto h -> esCompleto h
extraer-esCompleto completo-nil = tt
extraer-esCompleto (completo-bin h comp) = comp

heap-su-hijo-izq-es-heap : ∀ {i r d} -> Heap (bin i r d) -> Heap i
heap-su-hijo-izq-es-heap {i} {r} {d} h = record 
    { valido   = (heap-valido-su-hijo-izq-es-valido (Heap.valido h)) 
    ; completo = case (extraer-esCompleto (Heap.completo h)) of λ 
      {
        (inj₁ (_ , iperf , _)) -> completo-bin i (perfecto-implica-completo iperf)
      ; (inj₂ (_ , icomp , _)) -> completo-bin i icomp 
      }
    }

heap-su-hijo-der-es-heap : ∀ {i r d} -> Heap (bin i r d) -> Heap d
heap-su-hijo-der-es-heap {i} {r} {d} h = record 
    { valido = (heap-valido-su-hijo-der-es-valido (Heap.valido h)) 
    ; completo = case (extraer-esCompleto (Heap.completo h)) of λ 
        { 
          (inj₁ (_ , _ , dcomp)) -> completo-bin d dcomp
        ; (inj₂ (_ , _ , dperf)) -> completo-bin d (perfecto-implica-completo dperf)
        }
    }

insertar : ℕ -> AB -> AB
insertar n nil = bin nil n nil
insertar n (bin i r d) with n ≤? r | size i ≤? size d
-- Caso 1: n es menor que la raíz (r).
-- n se convierte en la nueva raíz y r "baja" al subárbol correspondiente.
... | yes n≤r | yes i≤d = bin (insertar r i) n d -- r baja al subárbol izquierdo (más pequeño).
... | yes n≤r | no  i>d = bin i n (insertar r d) -- r baja al subárbol derecho (más pequeño).

-- Caso 2: n NO es menor que la raíz (r).
-- r se mantiene como raíz y n se inserta en el subárbol correspondiente.
... | no ¬n≤r | yes i≤d = bin (insertar n i) r d -- n se inserta en el subárbol izquierdo.
... | no ¬n≤r | no  i>d = bin i r (insertar n d) -- n se inserta en el subárbol derecho.

hijo-izq : AB -> AB
hijo-izq nil = nil
hijo-izq (bin i r d) = i

hijo-der : AB -> AB
hijo-der nil = nil
hijo-der (bin i r d) = d

insertar-en-¬perf-mantiene-altura : ∀ {i r} -> (esPerfecto i -> ⊥) -> height (insertar r i) ≡ height i
insertar-en-¬perf-mantiene-altura {i} {r} = {!   !}

insertar-en-perf-aumenta-altura : ∀ {a k} -> esPerfecto a -> height (insertar k a) ≡ suc (height a)
insertar-en-perf-aumenta-altura {nil}       perf = refl
insertar-en-perf-aumenta-altura {bin i r d} {k} (hi≡hd , iperf , dperf) = {!   !}
-- insertar-en-perf-aumenta-altura {bin i r d} {k} (hi≡hd , iperf , dperf) with esPerfecto? d | esPerfecto? i
-- -- Casos absurdos
-- ... | yes dperf' | no ¬iperf = {!   !}
-- ... | no ¬dperf  | yes iperf' = {!   !}
-- ... | no ¬dperf  | no ¬iperf = {!   !}
-- -- Cuando ambos son perfectos, necesitamos coincidir con los with anidados de insertar-aux
-- ... | yes dperf' | yes iperf' with height i ≟ height d | height i ≟ suc (height d)
-- -- Caso: height i ≡ height d → insertamos en i
-- ...     | yes hi≡hd' | no _ =
--     let rec = insertar-en-perf-aumenta-altura {i} {k} iperf 
--     in cong suc (begin 
--     begin
--       height (insertar k i) ⊔ height d
--     ≡⟨ cong (_⊔ height d) rec ⟩ 
--       suc (height i) ⊔ height d
--     ≡⟨ cong (suc (height i) ⊔_) (sym hi≡hd) ⟩ 
--       suc (height i) ⊔ height i
--       -- TODO expandir esto, y por ahi probar aparte algun que otro import no tan justificado?
--     ≡⟨ trans (⊔-comm (suc (height i)) (height i)) (m≤n⇒m⊔n≡n (n≤1+n (height i))) ⟩ 
--       suc (height i)
--     ≡⟨ cong suc (sym (trans (cong (height i ⊔_) (sym hi≡hd)) (⊔-idem (height i)))) ⟩ 
--       suc (height i ⊔ height d)
--     ∎)
-- -- Subcasos restantes
-- ...     | yes _      | yes _ = {!   !}
-- ...     | no  _      | yes _ = {!   !}
-- ...     | no  _      | no  _ = {!   !}


-- Insertar en un árbol completo preserva la completitud (forma del árbol).
-- insertar-preserva-completo : ∀ {a} -> (n : ℕ) -> esCompleto a -> esCompleto (insertar n a)
-- insertar-preserva-completo {nil} n comp = inj₁ (refl , tt , tt)
-- insertar-preserva-completo {bin i r d} n (inj₁ (hi≡hd , iperf , dcomp)) with esPerfecto? d | esPerfecto? i 
-- -- Caso 1: i no es perfecto
-- ... | yes dperf | no ¬iperf  = ⊥-elim (¬iperf iperf)
-- -- Caso 1: i no es perfecto -> abs pues tenemos iperf
-- ... | no ¬dperf | no ¬iperf  = ⊥-elim (¬iperf iperf)

-- -- Caso 2: d no es perfecto, i es perfecto (misma altura) → insertamos en d
-- --trans hi≡hd (sym (insertar-en-¬perf-mantiene-altura ¬dperf))
-- ... | no ¬dperf | yes iperf  = inj₁ ({!   !} , iperf , insertar-preserva-completo n dcomp)
-- -- Caso 3: d e i son perfectos y de la misma altura → insertamos en i
-- ... | yes dperf | yes iperf with height i ≟ height d | height i ≟ suc (height d)
-- ...        | yes eq | no neq = inj₂ (trans (insertar-en-perf-aumenta-altura iperf) (cong suc hi≡hd) , insertar-preserva-completo n (perfecto-implica-completo iperf) , dperf)
-- -- subcasos imposibles por colision
-- ...        | no neq | _      = ⊥-elim (neq hi≡hd)
-- ...        | yes eq | yes k  = ⊥-elim {!   !}

--(? , insertar-preserva-completo n (perfecto-implica-completo iperf) , dperf)

-- -- insertar-preserva-completo {bin i r d} n (inj₂ (hi≡hd+1 , icomp , dperf)) with esPerfecto? d | esPerfecto? i 
-- -- ABSURDO
-- ... | no ¬dperf | yes iperf = ⊥-elim (¬dperf dperf)
-- -- ABSURDO
-- ... | no ¬dperf | no ¬iperf = ⊥-elim (¬dperf dperf)
-- -- 
-- -- Caso 1: d es perfecto e i no es perfecto → insertamos en i 
-- ... | yes dperf | no ¬iperf = inj₂ (trans (insertar-en-¬perf-mantiene-altura ¬iperf) hi≡hd+1 , insertar-preserva-completo n icomp , dperf)
-- -- Caso 2: ambos perfectos, distintas alturas -> insertamos en d
-- ... | yes dperf | yes iperf with height i ≟ height d | height i ≟ suc (height d)
-- ...        | no neq | yes eq = inj₁ (trans (hi≡hd+1) (sym (insertar-en-perf-aumenta-altura dperf)) , iperf , insertar-preserva-completo n (perfecto-implica-completo dperf))
-- -- subcasos imposibles por colision
-- ...        | no neq | _      = ⊥-elim {!   !}
-- ...        | yes eq | yes k  = ⊥-elim {!   !}
-- ...        | yes eq | no _   = ⊥-elim {!   !}


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
extraer-completo-izq (inj₂ (_ , inj₂ (hi≡hd+1 , icomp , dperf) , _)) = inj₂ (hi≡hd+1 , icomp , dperf)

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

insertar-preserva-completo : ∀ {h n} -> Heap h -> esCompleto (insertar n h)
insertar-preserva-completo h = {!   !}

insertar-preserva-validez : ∀ {a n} -> Heap a -> HeapValido (insertar n a)
insertar-preserva-validez {nil} h = heap-bin heap-nil heap-nil tt 
insertar-preserva-validez {bin i r d} {n} h = casesplit
  where 
    ival : HeapValido i
    ival = heap-valido-su-hijo-izq-es-valido (Heap.valido h)

    dval : HeapValido d
    dval = heap-valido-su-hijo-der-es-valido (Heap.valido h)

    iheap : Heap i
    iheap = heap-su-hijo-izq-es-heap h

    dheap : Heap d
    dheap = heap-su-hijo-der-es-heap h

    casesplit : HeapValido (insertar n (bin i r d))
    casesplit with n ≤? r | size i ≤? size d
    ... | yes n≤r | yes i≤d = heap-bin (insertar-preserva-validez iheap) dval ? 
    ... | yes n≤r | no  i>d = heap-bin ival (insertar-preserva-validez dheap) {!   !} 
    ... | no  n>r | no  i>d = heap-bin ival (insertar-preserva-validez dheap) {!   !}
    ... | no  n>r | yes i≤d = heap-bin (insertar-preserva-validez iheap) dval {!   !} 


insertar-preserva-invariante : ∀ {h n} -> Heap h -> Heap (insertar n h)
insertar-preserva-invariante {nil} {n} _ = record
  { valido = heap-bin heap-nil heap-nil tt
  ; completo = completo-bin (bin nil n nil) (inj₁ (refl , tt , tt))
  }

insertar-preserva-invariante {bin i r d} {n} h = record 
  { valido   = insertar-preserva-validez h
  ; completo = completo-bin (insertar n (bin i r d)) (insertar-preserva-completo h)
  }

