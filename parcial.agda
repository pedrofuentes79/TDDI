open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

infix  4 _~_
infixl 5 _U_
infixl 6 _∙_
infix  7 _*

-- El siguiente tipo de datos sirve para representar palabras en el alfabeto {0, 1}.
-- Por ejemplo, cons1 (cons1 (cons0 [])) represnta la cadena "110".
data Word : Set where
  []    : Word
  cons0 : Word → Word
  cons1 : Word → Word

-- Concatenación de palabras:
_++_ : Word -> Word -> Word
[]       ++ w2 = w2
cons0 w1 ++ w2 = cons0 (w1 ++ w2)
cons1 w1 ++ w2 = cons1 (w1 ++ w2)
-- El siguiente tipo de datos sirve para representar expresiones regulares en el alfabeto {0, 1}.
-- [Nota: el símbolo "∙" típicamente se puede ingresar tecleando "\."].
data RE : Set where
  ∅    : RE            -- Denota el lenguaje vacío.
  m[]  : RE            -- Denota el lenguaje que tiene sólo a la cadena vacía.
  m0   : RE            -- Denota el lenguaje que tiene sólo a la cadena "0".
  m1   : RE            -- Denota el lenguaje que tiene sólo a la cadena "1".
  _U_  : RE → RE → RE  -- (R U S) denota la unión de los lenguajes denotados por R y S.
  _∙_  : RE → RE → RE  -- (R ∙ S) denota la concatenación de los lenguajes denotados por R y S.
  _*   : RE → RE       -- (R *) denota la clausura de Kleene del lenguaje denotado por R.

-- El predicado (Match R w) está habitado cuando w está en el lenguaje denotado por R.
data Match : RE → Word → Set where
  Match-[] : Match m[] []
  Match-0  : Match m0 (cons0 [])
  Match-1  : Match m1 (cons1 [])
  Match-U1 : {R S : RE} {w : Word}
           → Match R w
           → Match (R U S) w
  Match-U2 : {R S : RE} {w : Word}
           → Match S w
           → Match (R U S) w
  Match-∙  : {R S : RE} {w1 w2 : Word}
           → Match R w1
           → Match S w2
           → Match (R ∙ S) (w1 ++ w2)
  Match-*1 : {R : RE} → Match (R *) []
  Match-*2 : {R : RE} {w1 w2 : Word}
           → Match R w1
           → Match (R *) w2
           → Match (R *) (w1 ++ w2)

---

-- Ejercicio 1: demostrar que la expresión regular (m0 U m1)* matchea a cualquier palabra.
-- Sugerencia: proceder por inducción en w.
lenguaje-completo : {w : Word} → Match ((m0 U m1) *) w
lenguaje-completo {[]} = Match-*1
lenguaje-completo {cons0 w} = Match-*2 (Match-U1 Match-0) (lenguaje-completo {w})
lenguaje-completo {cons1 w} = Match-*2 (Match-U2 Match-1) (lenguaje-completo {w})

---

-- Decimos que dos expresiones regulares son equivalentes si denotan el mismo lenguaje,
-- es decir, matchean las mismas palabras.
_~_ : RE → RE → Set
R ~ S = (w : Word) → ((Match R w → Match S w) × (Match S w → Match R w))

-- Ejercicio 2: demostrar que _~_ es una relación de equivalencia.

~-refl : {R : RE} → R ~ R
~-refl w = (λ match -> match)
         , (λ match -> match)

~-sym : {R S : RE} → R ~ S → S ~ R
~-sym R~S w = proj₂ (R~S w)
            , proj₁ (R~S w)

~-trans : {R S T : RE} → R ~ S → S ~ T → R ~ T
~-trans R~S S~T w = (λ m → proj₁ (S~T w) (proj₁ (R~S w) m))
                  , (λ m → proj₂ (R~S w) (proj₂ (S~T w) m))

----

-- Ejercicio 3: demostrar que la unión es conmutativa y asociativa
-- y que el vacío es el elemento neutro.

U-comm : {R S : RE} → R U S ~ S U R
U-comm w =  (λ { (Match-U1 p) -> Match-U2 p
               ; (Match-U2 p) -> Match-U1 p
               })
          , (λ { (Match-U1 p) -> Match-U2 p
               ; (Match-U2 p) -> Match-U1 p
               })

U-assoc : {R S T : RE} → (R U S) U T ~ R U (S U T)
U-assoc w = (λ { (Match-U1 (Match-U1 p)) -> Match-U1 p
               ; (Match-U1 (Match-U2 p)) -> Match-U2 (Match-U1 p)
               ; (Match-U2 p)            -> Match-U2 (Match-U2 p)
               })
          , (λ { (Match-U1 p)            -> Match-U1 (Match-U1 p)
               ; (Match-U2 (Match-U1 p)) -> Match-U1 (Match-U2 p)
               ; (Match-U2 (Match-U2 p)) -> Match-U2 p
          })

U-neut : {R : RE} → R U ∅ ~ R
U-neut w = (λ { (Match-U1 p) -> p
              ; (Match-U2 ()) -- pues no es posible que esté en vacío
              })
         , (λ matchR -> Match-U1 matchR)

----

-- Ejercicio 4: demostrar que la concatenación es asociativa
-- y que el lenguaje que incluye sólo a la palabra vacía es el elemento neutro.
-- Para hacer este ejercicio puede ser necesario probar lemas auxiliares
-- sobre la concatenación de palabras y usar transportes.

++-assoc : (w1 w2 w3 : Word) -> (w1 ++ w2) ++ w3 ≡ w1 ++ (w2 ++ w3)
++-assoc []        w2 w3 = refl
++-assoc (cons0 w1) w2 w3 = cong cons0 (++-assoc w1 w2 w3)
++-assoc (cons1 w1) w2 w3 = cong cons1 (++-assoc w1 w2 w3)

++-neut-r : (w : Word) -> w ++ [] ≡ w
++-neut-r []        = refl
++-neut-r (cons0 w) = cong cons0 (++-neut-r w)
++-neut-r (cons1 w) = cong cons1 (++-neut-r w)

∙-assoc : {R S T : RE} → (R ∙ S) ∙ T ~ R ∙ (S ∙ T)
∙-assoc {R} {S} {T} w =
    (λ { (Match-∙ {w2 = w3} (Match-∙ {w1 = w1} {w2 = w2} pR pS) pT) ->
        -- tengo (w1 ++ w2) ++ w3 y quiero w1 ++ (w2 ++ w3)
         subst 
              (Match (R ∙ (S ∙ T)))         -- el tipo final
              (sym (++-assoc w1 w2 w3))     -- prueba de que son iguales 
              (Match-∙ pR (Match-∙ pS pT))  -- Match final
        })
        -- Lo mismo pero al reves
  , (λ { (Match-∙ {w1 = w1} pR (Match-∙ {w1 = w2} {w2 = w3} pS pT)) ->
         subst 
              (Match ((R ∙ S) ∙ T)) 
              (++-assoc w1 w2 w3) 
              (Match-∙ (Match-∙ pR pS) pT) 
        })

∙-neut : {R : RE} → R ∙ m[] ~ R
-- Ida: voy de (w ++ []) a w
∙-neut {R} w = (λ {(Match-∙ {w1 = w1} pR Match-[] ) -> subst (Match R) (sym (++-neut-r w1)) pR})
-- No hace falta el pattern matching aca porque pR es "Match R w"
             , (λ pR -> subst (Match (R ∙ m[])) (++-neut-r w) (Match-∙ pR (Match-[])))

----

-- La siguiente operación invierte una palabra.
reverse : Word → Word
reverse []        = []
reverse (cons0 w) = reverse w ++ cons0 []
reverse (cons1 w) = reverse w ++ cons1 []

-- Ejercicio 5: definir una expresión regular que reconozca el reverso del lenguaje original,
-- es decir, vale (Match R w) si y sólo si vale (Match (rev R) (reverse w))
rev : RE → RE
rev ∅       = ∅
rev m[]     = m[]
rev m0      = m0
rev m1      = m1
rev (R U S) = rev R U rev S
rev (R ∙ S) = rev S ∙ rev R
rev (R *)   = (rev R) *


-- Ejercicio 6: demostrar que el lenguaje de (rev R) incluye el reverso de todas las palabras de R.
-- Sugerencia: proceder por inducción en la derivación de (Match R w).
-- Para hacer este ejercicio puede ser necesario probar lemas auxiliares sobre palabras
-- y usar transportes.

-- Lema: reverse distribuye sobre ++ invirtiendo el orden
reverse-++ : (w1 w2 : Word) -> reverse (w1 ++ w2) ≡ reverse w2 ++ reverse w1
reverse-++ []         w2 = sym (++-neut-r (reverse w2))
reverse-++ (cons0 w1) w2 = begin
    reverse (cons0 w1 ++ w2)
  ≡⟨ refl ⟩
    reverse (w1 ++ w2) ++ cons0 []
  ≡⟨ cong (_++ cons0 []) (reverse-++ w1 w2) ⟩ -- HI
    (reverse w2 ++ reverse w1) ++ cons0 []
  ≡⟨ ++-assoc (reverse w2) (reverse w1) (cons0 []) ⟩
    reverse w2 ++ (reverse w1 ++ cons0 [])
  ≡⟨ refl ⟩
    reverse w2 ++ reverse (cons0 w1)
  ∎
-- Lo mismo! Pero con cons1
reverse-++ (cons1 w1) w2 = begin
    reverse (cons1 w1 ++ w2)
  ≡⟨ refl ⟩
    reverse (w1 ++ w2) ++ cons1 []
  ≡⟨ cong (_++ cons1 []) (reverse-++ w1 w2) ⟩ -- HI
    (reverse w2 ++ reverse w1) ++ cons1 []
  ≡⟨ ++-assoc (reverse w2) (reverse w1) (cons1 []) ⟩
    reverse w2 ++ (reverse w1 ++ cons1 [])
  ≡⟨ refl ⟩
    reverse w2 ++ reverse (cons1 w1)
  ∎

-- Lema: podemos extender un match de R* 
extender-match-R* : {R : RE} {w1 w2 : Word} -> Match (R *) w1 -> Match R w2 -> Match (R *) (w1 ++ w2)
-- Se queja si no pongo el "."
-- Hacemos inducción sobre "Match (R *) w1"; cuando es la palabra vacía y cuando es concatenación
extender-match-R* {R} {w1 = .[]} {w2} Match-*1 p = 
  subst 
      (Match (R *)) 
      (++-neut-r w2) 
      (Match-*2 p Match-*1)
extender-match-R* {R} {w1 = .(w1' ++ w2')} {w2} (Match-*2 {w1 = w1'} {w2 = w2'} q1 q2) p = 
  subst 
      (Match (R *)) 
      (sym (++-assoc w1' w2' w2)) 
      (Match-*2 q1 (extender-match-R* q2 p))


match-rev : {R : RE} {w : Word} → Match R w → Match (rev R) (reverse w)
match-rev Match-[]       = Match-[]
match-rev Match-0        = Match-0
match-rev Match-1        = Match-1
match-rev (Match-U1 p)   = Match-U1 (match-rev p)
match-rev (Match-U2 p)   = Match-U2 (match-rev p)
match-rev (Match-∙ {R} {S} {w1 = w1} {w2 = w2} p q) = 
  subst 
       (Match (rev (R ∙ S)))
       (sym (reverse-++ w1 w2))
       -- Aca tengo que armar "Match (rev (R ∙ S)) (reverse w2 ++ reverse w1)", que es:
       (Match-∙ (match-rev q) (match-rev p))

match-rev Match-*1       = Match-*1
match-rev (Match-*2 {R = R} {w1 = w1} {w2 = w2} p q) = 
    subst 
        (Match ((rev R) *)) 
        (sym (reverse-++ w1 w2)) 
        (extender-match-R* (match-rev q) (match-rev p))

