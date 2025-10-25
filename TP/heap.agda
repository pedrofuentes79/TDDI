open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _+_; _∸_; _<_; _>_; s≤s; z≤n)
open import Data.Nat.Properties using (_≤?_; _≟_; ≤-trans; ≤-total; ⊔-idem; ⊔-comm; m≤n⇒m⊔n≡n; ⊔-identityʳ; n≤1+n)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Relation.Binary.PropositionalEquality using (subst)

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


heap-completo-su-hijo-der-es-completo : ∀ {i r d} -> HeapCompleto (bin i r d) -> esCompleto d
heap-completo-su-hijo-der-es-completo (completo-bin _ (inj₁ (_ , _ , dcomp))) = dcomp 
heap-completo-su-hijo-der-es-completo (completo-bin _ (inj₂ (_ , _ , dperf))) = perfecto-implica-completo dperf

heap-completo-su-hijo-izq-es-completo : ∀ {i r d} -> HeapCompleto (bin i r d) -> esCompleto i
heap-completo-su-hijo-izq-es-completo (completo-bin _ (inj₁ (_ , iperf , _))) = perfecto-implica-completo iperf
heap-completo-su-hijo-izq-es-completo (completo-bin _ (inj₂ (_ , icomp , _))) = icomp

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
insertar n (bin i r d) with n ≤? r | esPerfecto? i | esPerfecto? d | height i ≟ height d 
-- Caso 1: n es menor que la raíz (r).
-- n se convierte en la nueva raíz y r "baja" al subárbol correspondiente.
... | yes n≤r | yes iperf | yes dperf | yes hi≡hd = bin (insertar r i) n d 
... | yes n≤r | yes iperf | yes dperf | no      _ = bin i n (insertar r d)
... | yes n≤r | yes iperf | no ¬dperf | _ = bin i n (insertar r d) 
... | yes n≤r | no ¬iperf | no ¬dperf | _ = bin (insertar r i) n d  -- No deberia suceder,insertamos en izquierda para "arreglarlo"
... | yes n≤r | no ¬iperf | yes dperf | _ = bin (insertar r i) n d

-- Caso 2: n NO es menor que la raíz (r).
-- r se mantiene como raíz y n se inserta en el subárbol correspondiente.
... | no  n>r | yes iperf | no ¬dperf | _ = bin i r (insertar n d) 
... | no  n>r | no ¬iperf | no ¬dperf | _ = bin (insertar n i) r d  -- No deberia suceder,insertamos en izquierda para "arreglarlo"
... | no  n>r | no ¬iperf | yes dperf | _ = bin (insertar n i) r d
... | no  n>r | yes iperf | yes dperf | yes hi≡hd = bin (insertar n i) r d 
     -- Si la altura es igual y ambos son perfectos, insertamos en i. Si i es mas alto, insertamos en dk
... | no  n>r | yes iperf | yes dperf | no _ = bin i r (insertar n d)

heap-completo-alguno-de-sus-hijos-es-perfecto : ∀ {i r d} -> esCompleto (bin i r d) -> (esPerfecto i -> ⊥) -> (esPerfecto d -> ⊥) -> ⊥
heap-completo-alguno-de-sus-hijos-es-perfecto (inj₁ (_ , iperf , _)) ¬iperf _ = ¬iperf iperf
heap-completo-alguno-de-sus-hijos-es-perfecto (inj₂ (_ , _ , dperf)) _ ¬dperf = ¬dperf dperf

hijo-izq : AB -> AB
hijo-izq nil = nil
hijo-izq (bin i r d) = i

hijo-der : AB -> AB
hijo-der nil = nil
hijo-der (bin i r d) = d

si-difieren-en-altura-i-es-d+1 : ∀ {i r d} -> esCompleto (bin i r d) -> (height i ≡ height d -> ⊥) -> height i ≡ suc (height d)
si-difieren-en-altura-i-es-d+1 (inj₁ (hi≡hd , _ , _)) hi≠hd = ⊥-elim (hi≠hd hi≡hd)
si-difieren-en-altura-i-es-d+1 (inj₂ (hi≡hd+1 , _ , _)) hi≠hd = hi≡hd+1


insertar-en-perf-aumenta-altura : ∀ {a n} -> esPerfecto a -> height (insertar n a) ≡ suc (height a)
insertar-en-perf-aumenta-altura {nil}       perf = refl
insertar-en-perf-aumenta-altura {bin i₁ r₁ d₁} {r} (hi≡hd , iperf , dperf) 
-- Tengo que preguntar esPerfecto? i₁ , esPerfecto? d₁ porque si no, no unifica insertar :D
  with r ≤? r₁ | esPerfecto? i₁ | esPerfecto? d₁ | height i₁ ≟ height d₁
-- ABSURDOS: se que vale iperf y dperf
... | _        | no ¬iperf | _         | _         = ⊥-elim (¬iperf iperf)
... | _        | _         | no ¬dperf | _         = ⊥-elim (¬dperf dperf)
-- ABSURDO: se que hi≡hd
... | _        | _         | _         | no  hi≠hd = ⊥-elim (hi≠hd hi≡hd)
... | yes r≤r₁ | yes iperf | yes dperf | yes hi≡hd = cong suc (
      begin
        height (insertar r₁ i₁) ⊔ height d₁
      ≡⟨ cong (_⊔ height d₁) (insertar-en-perf-aumenta-altura iperf) ⟩ 
        suc (height i₁) ⊔ height d₁
      ≡⟨ cong (suc (height i₁) ⊔_) (sym hi≡hd) ⟩
        suc (height i₁) ⊔ height i₁
      ≡⟨ trans (⊔-comm (suc (height i₁)) (height i₁)) (m≤n⇒m⊔n≡n (n≤1+n (height i₁))) ⟩
        suc (height i₁)
      ≡⟨ cong suc (sym (⊔-idem (height i₁))) ⟩
        suc (height i₁ ⊔ height i₁)
      ≡⟨ cong suc (cong (height i₁ ⊔_) hi≡hd) ⟩
        suc (height i₁ ⊔ height d₁)
      ∎)
-- La misma demo, pero con r en vez de r₁
... | no  r>r₁ | yes iperf | yes dperf | yes hi≡hd = cong suc (
      begin
        height (insertar r i₁) ⊔ height d₁
      ≡⟨ cong (_⊔ height d₁) (insertar-en-perf-aumenta-altura iperf) ⟩ 
        suc (height i₁) ⊔ height d₁
      ≡⟨ cong (suc (height i₁) ⊔_) (sym hi≡hd) ⟩
        suc (height i₁) ⊔ height i₁
      ≡⟨ trans (⊔-comm (suc (height i₁)) (height i₁)) (m≤n⇒m⊔n≡n (n≤1+n (height i₁))) ⟩
        suc (height i₁)
      ≡⟨ cong suc (sym (⊔-idem (height i₁))) ⟩
        suc (height i₁ ⊔ height i₁)
      ≡⟨ cong suc (cong (height i₁ ⊔_) hi≡hd) ⟩
        suc (height i₁ ⊔ height d₁)
      ∎)

insertar-en-¬perf-mantiene-altura : ∀ {a n} -> esCompleto a -> (esPerfecto a -> ⊥) -> height (insertar n a) ≡ height a
insertar-en-¬perf-mantiene-altura {nil} _ ¬perf = ⊥-elim (¬perf tt)
insertar-en-¬perf-mantiene-altura {bin i₁ r₁ d₁} {r} comp ¬perf 
  with r ≤? r₁ | esPerfecto? i₁ | esPerfecto? d₁ | height i₁ ≟ height d₁
-- ABS: ambos perfectos y misma altura → absurdo
... | _  | yes iperf | yes dperf | yes hi≡hd = ⊥-elim (¬perf (hi≡hd , iperf , dperf))
-- ABS: alguno de los dos debe ser perfecto
... | _ | no ¬iperf | no ¬dperf | _ = ⊥-elim (heap-completo-alguno-de-sus-hijos-es-perfecto {r = r₁} comp ¬iperf ¬dperf)
-- Caso: ambos perfectos pero distinta altura → insertamos en d₁
... | yes r≤r₁ | yes iperf | yes dperf | no  hi≠hd = cong suc (
    begin
      height i₁ ⊔ height (insertar r₁ d₁)
    ≡⟨ cong (λ z -> z ⊔ height (insertar r₁ d₁)) (si-difieren-en-altura-i-es-d+1 {r = r₁} comp (hi≠hd)) ⟩ 
      suc (height d₁) ⊔ height (insertar r₁ d₁)
    ≡⟨ cong (λ z -> suc (height d₁) ⊔ z) (insertar-en-perf-aumenta-altura dperf) ⟩ 
      suc (height d₁) ⊔ suc (height d₁) 
    ≡⟨ ⊔-idem (suc (height d₁)) ⟩ 
      suc (height d₁)
    ≡⟨ sym (trans (⊔-comm (suc (height d₁)) (height d₁)) (m≤n⇒m⊔n≡n (n≤1+n (height d₁)))) ⟩ 
      suc (height d₁) ⊔ height d₁
    ≡⟨ cong (_⊔ height d₁) (sym (si-difieren-en-altura-i-es-d+1 {r = r₁} comp (hi≠hd))) ⟩ 
      height i₁ ⊔ height d₁
    ∎)
-- Literal la misma demo que arriba pero con r en vez de r₁. Se podria extraer el lema y parametrizarla... en otra vida
... | no r>r₁ | yes iperf | yes dperf | no  hi≠hd = cong suc (
    begin
      height i₁ ⊔ height (insertar r d₁)
    ≡⟨ cong (λ z -> z ⊔ height (insertar r d₁)) (si-difieren-en-altura-i-es-d+1 {r = r} comp (hi≠hd)) ⟩ 
      suc (height d₁) ⊔ height (insertar r d₁)
    ≡⟨ cong (λ z -> suc (height d₁) ⊔ z) (insertar-en-perf-aumenta-altura dperf) ⟩ 
      suc (height d₁) ⊔ suc (height d₁) 
    ≡⟨ ⊔-idem (suc (height d₁)) ⟩ 
      suc (height d₁)
    ≡⟨ sym (trans (⊔-comm (suc (height d₁)) (height d₁)) (m≤n⇒m⊔n≡n (n≤1+n (height d₁)))) ⟩ 
      suc (height d₁) ⊔ height d₁
    ≡⟨ cong (_⊔ height d₁) (sym (si-difieren-en-altura-i-es-d+1 {r = r} comp (hi≠hd))) ⟩ 
      height i₁ ⊔ height d₁
    ∎)
-- Caso: i perfecto, d no perfecto → insertamos en d₁
... | yes r≤r₁ | yes iperf | no ¬dperf | _ = cong suc (
    begin
      height i₁ ⊔ height (insertar r₁ d₁)
    ≡⟨ cong (λ z -> height i₁ ⊔ z) (insertar-en-¬perf-mantiene-altura (heap-completo-su-hijo-der-es-completo (completo-bin (bin i₁ r₁ d₁) comp)) ¬dperf) ⟩
      height i₁ ⊔ height d₁
    ∎)
-- Caso: r > r₁, i perfecto, d no perfecto → insertamos en d₁
-- Demo analoga a la de arriba, la pongo inline para que moleste menos
... | no r>r₁ | yes iperf | no ¬dperf | _ = cong suc (cong (λ z -> height i₁ ⊔ z) (insertar-en-¬perf-mantiene-altura (heap-completo-su-hijo-der-es-completo (completo-bin (bin i₁ r₁ d₁) comp)) ¬dperf))
-- Caso: i no perfecto → insertamos en i₁
-- Demo analoga, solo que pidiendo mantener altura en i₁
... | yes r≤r₁ | no ¬iperf | yes dperf | _ = cong suc (cong (_⊔ height d₁) (insertar-en-¬perf-mantiene-altura (heap-completo-su-hijo-izq-es-completo (completo-bin (bin i₁ r₁ d₁) comp)) ¬iperf))
-- Misma demo.
... | no  r>r₁ | no ¬iperf | yes dperf | _ = cong suc (cong (_⊔ height d₁) (insertar-en-¬perf-mantiene-altura (heap-completo-su-hijo-izq-es-completo (completo-bin (bin i₁ r₁ d₁) comp)) ¬iperf))

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

extraer-rmqh-heapvalido : ∀ {a} -> HeapValido a -> raizMenorQueHijos a
extraer-rmqh-heapvalido heap-nil = tt
extraer-rmqh-heapvalido (heap-bin _ _ rmqh) = rmqh

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

completo-hi≠hd-implica-dperf : ∀ {i r d} -> esCompleto (bin i r d) -> (height i ≡ height d → ⊥) -> esPerfecto d
completo-hi≠hd-implica-dperf (inj₁ (hi≡hd , _ , _))     hi≠hd = ⊥-elim (hi≠hd hi≡hd)
completo-hi≠hd-implica-dperf (inj₂ (_ , _ , dperf))     hi≠hd = dperf

completo-hi≡hd-implica-iperf : ∀ {i r d} -> esCompleto (bin i r d) -> (height i ≡ height d) -> esPerfecto i
completo-hi≡hd-implica-iperf (inj₁ (_ , iperf , _))     hi≡hd = iperf
completo-hi≡hd-implica-iperf (inj₂ (hi≡shd , _ , _))    hi≡hd = ⊥-elim (absurdo₁ hi≡hd hi≡shd)

insertar-preserva-completo : ∀ {a n} -> Heap a -> esCompleto (insertar n a)
insertar-preserva-completo {nil} {n} h = inj₁ (refl , tt , tt) 
insertar-preserva-completo {bin i r d} {n} h = casesplit
  where
    todocomp : esCompleto (bin i r d)
    todocomp = extraer-esCompleto (Heap.completo h)
    iheap : Heap i
    iheap = heap-su-hijo-izq-es-heap h
    dheap : Heap d
    dheap = heap-su-hijo-der-es-heap h
    dcomp : esCompleto d
    dcomp = heap-completo-su-hijo-der-es-completo (Heap.completo h)
    icomp : esCompleto i
    icomp = heap-completo-su-hijo-izq-es-completo (Heap.completo h)


    casesplit : esCompleto (insertar n (bin i r d))
    casesplit with n ≤? r | esPerfecto? i | esPerfecto? d | height i ≟ height d
    -- absurdo, alguno de los dos deberia ser perfecto
    ... | _        | no ¬iperf | no ¬dperf | _         = ⊥-elim (heap-completo-alguno-de-sus-hijos-es-perfecto {i} {r} {d} todocomp ¬iperf ¬dperf)
    -- absurdo. No pueden tener alturas distintas y que d no sea perfecto
    ... | _        | yes iperf | no ¬dperf | no  hi≠hd = ⊥-elim (¬dperf (completo-hi≠hd-implica-dperf {r = r} todocomp hi≠hd))
    -- este caso es absurdo. No puede ser que ¬iperf, dperf y hi≡hd
    ... | _        | no ¬iperf | yes dperf | yes hi≡hd = ⊥-elim (¬iperf (completo-hi≡hd-implica-iperf {r = r} todocomp hi≡hd))
    ... | yes r≤r₁ | yes iperf | no ¬dperf | yes hi≡hd = inj₁ (trans hi≡hd (sym (insertar-en-¬perf-mantiene-altura dcomp ¬dperf)) , iperf , (insertar-preserva-completo dheap))
    ... | no  r>r₁ | yes iperf | no ¬dperf | yes hi≡hd = inj₁ (trans hi≡hd (sym (insertar-en-¬perf-mantiene-altura dcomp ¬dperf)) , iperf , (insertar-preserva-completo dheap))
    ... | yes r≤r₁ | yes iperf | yes dperf | yes hi≡hd = inj₂ (trans (insertar-en-perf-aumenta-altura iperf) (cong suc hi≡hd) , (insertar-preserva-completo iheap) , dperf)
    ... | yes r≤r₁ | yes iperf | yes dperf | no  hi≠hd = inj₁ (trans (si-difieren-en-altura-i-es-d+1 {r = r} todocomp hi≠hd) (sym (insertar-en-perf-aumenta-altura dperf)) , iperf , (insertar-preserva-completo dheap))
    ... | yes r≤r₁ | no ¬iperf | yes dperf | no  hi≠hd = inj₂ (trans (insertar-en-¬perf-mantiene-altura icomp ¬iperf) (si-difieren-en-altura-i-es-d+1 {r = r} todocomp hi≠hd) , (insertar-preserva-completo iheap) , dperf)
    ... | no  r>r₁ | no ¬iperf | yes dperf | no  hi≠hd = inj₂ (trans (insertar-en-¬perf-mantiene-altura icomp ¬iperf) (si-difieren-en-altura-i-es-d+1 {r = n} todocomp hi≠hd) , (insertar-preserva-completo iheap) , dperf)
    ... | no  r>r₁ | yes iperf | yes dperf | yes hi≡hd = inj₂ (trans (insertar-en-perf-aumenta-altura iperf) (cong suc hi≡hd) , (insertar-preserva-completo iheap) , dperf)
    ... | no  r>r₁ | yes iperf | yes dperf | no  hi≠hd = inj₁ (trans (si-difieren-en-altura-i-es-d+1 {r = n} todocomp hi≠hd) (sym (insertar-en-perf-aumenta-altura dperf)) , iperf , (insertar-preserva-completo dheap))





raizMenor-post-insercion-caso1 : ∀ {n r} (i d : AB) → (h-valido : HeapValido (bin i r d)) → (n≤k : n ≤ r) → 
                                 raizMenorQueHijos (bin (insertar r i) n d)
raizMenor-post-insercion-caso1 nil nil h-valido n≤r  = n≤r
raizMenor-post-insercion-caso1 nil (bin i₁ r₁ d₁) (heap-bin _ _ rmqh) n≤r = (n≤r , ≤-trans n≤r rmqh)
raizMenor-post-insercion-caso1 {n} {r} (bin i₁ r₁ d₁) nil (heap-bin ival dval rmqh) n≤r with r ≤? r₁ | esPerfecto? i₁ | esPerfecto? d₁ | height i₁ ≟ height d₁
... | yes r≤r₁ | no ¬iperf | no ¬dperf | _ = n≤r
... | yes r≤r₁ | yes iperf | no ¬dperf | _ = n≤r
... | yes r≤r₁ | no ¬iperf | yes dperf | _ = n≤r
... | yes r≤r₁ | yes iperf | yes dperf | yes hi≡hd  = n≤r
... | yes r≤r₁ | yes iperf | yes dperf | no hi≡hd+1 = n≤r
... | no  r>r₁ | yes iperf | no ¬dperf | _ = ≤-trans n≤r rmqh
... | no  r>r₁ | no ¬iperf | yes dperf | _ = ≤-trans n≤r rmqh
... | no  r>r₁ | no ¬iperf | no ¬dperf | _ = ≤-trans n≤r rmqh
... | no  r>r₁ | yes iperf | yes dperf | yes hi≡hd = ≤-trans n≤r rmqh
... | no  r>r₁ | yes iperf | yes dperf | no _ = ≤-trans n≤r rmqh
raizMenor-post-insercion-caso1 {n} {r} (bin i₁ r₁ d₁) (bin i₂ r₂ d₂) (heap-bin ival dval (r≤r₁ , r≤r₂)) n≤r with r ≤? r₁ | esPerfecto? i₁ | esPerfecto? d₁ | height i₁ ≟ height d₁
... | yes r≤r₁ | no ¬iperf | no ¬dperf | _ = (n≤r , ≤-trans n≤r r≤r₂)
... | yes r≤r₁ | yes iperf | no ¬dperf | _ = (n≤r , ≤-trans n≤r r≤r₂)
... | yes r≤r₁ | no ¬iperf | yes dperf | _ = (n≤r , ≤-trans n≤r r≤r₂)
... | yes r≤r₁ | yes iperf | yes dperf | yes hi≡hd  = (n≤r , ≤-trans n≤r r≤r₂)
... | yes r≤r₁ | yes iperf | yes dperf | no hi≡hd+1 = (n≤r , ≤-trans n≤r r≤r₂)
... | no  r>r₁ | yes iperf | no ¬dperf | _ = ⊥-elim (r>r₁ r≤r₁)
... | no  r>r₁ | no ¬iperf | yes dperf | _ = ⊥-elim (r>r₁ r≤r₁)
... | no  r>r₁ | no ¬iperf | no ¬dperf | _ = ⊥-elim (r>r₁ r≤r₁)
... | no  r>r₁ | yes iperf | yes dperf | yes hi≡hd = ⊥-elim (r>r₁ r≤r₁)
... | no  r>r₁ | yes iperf | yes dperf | no _ = ⊥-elim (r>r₁ r≤r₁)



raizMenor-post-insercion-caso2 : ∀ {n r} (i d : AB) → (h-valido : HeapValido (bin i r d)) → (n>r : (n ≤ r -> ⊥)) → 
                                 raizMenorQueHijos (bin (insertar n i) r d)
raizMenor-post-insercion-caso2 = {!   !}

raizMenor-post-insercion-caso3 : ∀ {n r} (i d : AB) → (h-valido : HeapValido (bin i r d)) → (n>r : (n ≤ r -> ⊥)) → 
                                 raizMenorQueHijos (bin i r (insertar n d))
raizMenor-post-insercion-caso3 = {!   !}


raizMenor-post-insercion-caso4 : ∀ {n r} (i d : AB) → (h-valido : HeapValido (bin i r d)) → (n>r : (n ≤ r -> ⊥)) → 
                                 raizMenorQueHijos (bin i n (insertar r d))
raizMenor-post-insercion-caso4 = {!   !}


raizMenor-post-insercion-caso5 : ∀ {n r} (i d : AB) → (h-valido : HeapValido (bin i r d)) → (n>r : n ≤ r) → 
                                 raizMenorQueHijos (bin i n (insertar r d))
raizMenor-post-insercion-caso5 = {!   !}

insertar-preserva-validez : ∀ {a n} -> Heap a -> HeapValido (insertar n a)
insertar-preserva-validez {nil} h = heap-bin heap-nil heap-nil tt 
insertar-preserva-validez {bin i r d} {n} h = casesplit
  where 
    ival : HeapValido i
    ival = heap-valido-su-hijo-izq-es-valido (Heap.valido h)

    hval : HeapValido (bin i r d)
    hval = Heap.valido h

    dval : HeapValido d
    dval = heap-valido-su-hijo-der-es-valido (Heap.valido h)

    iheap : Heap i
    iheap = heap-su-hijo-izq-es-heap h

    dheap : Heap d
    dheap = heap-su-hijo-der-es-heap h

    casesplit : HeapValido (insertar n (bin i r d))
    casesplit with n ≤? r | esPerfecto? i | esPerfecto? d | height i ≟ height d
    ... | yes n≤r | yes iperf | yes dperf | yes _ = heap-bin (insertar-preserva-validez iheap) dval (raizMenor-post-insercion-caso1 i d hval n≤r)
    ... | yes n≤r | yes iperf | yes dperf | no  _ = heap-bin ival (insertar-preserva-validez dheap) (raizMenor-post-insercion-caso5 i d hval n≤r)
    ... | yes n≤r | yes iperf | no ¬dperf | _     = heap-bin ival (insertar-preserva-validez dheap) (raizMenor-post-insercion-caso5 i d hval n≤r)
    ... | yes n≤r | no ¬iperf | yes dperf | _     = heap-bin (insertar-preserva-validez iheap) dval (raizMenor-post-insercion-caso1 i d hval n≤r)
    ... | yes n≤r | no ¬iperf | no ¬dperf | _     = heap-bin (insertar-preserva-validez iheap) dval (raizMenor-post-insercion-caso1 i d hval n≤r)

    ... | no  n>r | yes iperf | no ¬dperf | _     = heap-bin ival (insertar-preserva-validez dheap) (raizMenor-post-insercion-caso3 i d hval n>r)
    ... | no  n>r | no ¬iperf | yes dperf | _     = heap-bin (insertar-preserva-validez iheap) dval (raizMenor-post-insercion-caso2 i d hval n>r)
    ... | no  n>r | no ¬iperf | no ¬dperf | _     = heap-bin (insertar-preserva-validez iheap) dval (raizMenor-post-insercion-caso2 i d hval n>r)
    ... | no  n>r | yes iperf | yes dperf | yes _ = heap-bin (insertar-preserva-validez iheap) dval (raizMenor-post-insercion-caso2 i d hval n>r)
    ... | no  n>r | yes iperf | yes dperf | no  _ = heap-bin ival (insertar-preserva-validez dheap) (raizMenor-post-insercion-caso3 i d hval n>r)

insertar-preserva-invariante : ∀ {h n} -> Heap h -> Heap (insertar n h)
insertar-preserva-invariante {nil} {n} _ = record
  { valido = heap-bin heap-nil heap-nil tt
  ; completo = completo-bin (bin nil n nil) (inj₁ (refl , tt , tt))
  }

insertar-preserva-invariante {bin i r d} {n} h = record 
  { valido   = insertar-preserva-validez {bin i r d} {n} h
  ; completo = completo-bin (insertar n (bin i r d)) (insertar-preserva-completo {bin i r d} {n} h)
  }

