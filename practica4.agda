
open import Data.Unit
       using (⊤; tt)
open import Data.Empty
       using (⊥; ⊥-elim)
open import Data.Bool
       using (Bool; true; false)
open import Data.Nat
       using (ℕ; zero; suc; _+_)
open import Data.Sum
       using (_⊎_; inj₁; inj₂)
open import Data.Product
       using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality
       using (_≡_; refl; sym; trans; cong)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

-- Definimos la composición:
infixr 80 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) a = g (f a)

-- Parte A --

-- Recordemos la definición del tipo de datos de las listas:

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- Recordemos la definición de algunas funciones básicas:

map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- A.1) Demostrar que map conmuta con la concatenación:
map-++ : {A B : Set} {f : A → B} {xs ys : List A}
       → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ {A} {B} {f} {[]} {ys} = refl
    -- begin
    --     map f ([] ++ ys)
    -- ≡⟨ cong (map f) (refl)⟩
    --     map f ys 
    -- ≡⟨ sym refl ⟩ 
    --     [] ++ map f ys
    -- ≡⟨ cong (λ z -> z ++ map f ys) (refl) ⟩ 
    --     map f [] ++ map f ys
    -- ∎

map-++ {A} {B} {f} {x ∷ xs} {ys} = 
    begin
       map f ((x ∷ xs) ++ ys)
    ≡⟨ refl ⟩
       map f (x ∷ (xs ++ ys)) 
    ≡⟨ refl ⟩
       f x ∷ (map f (xs ++ ys)) 
    ≡⟨ cong (λ z -> f x ∷ z) (map-++ {xs = xs} {ys = ys}) ⟩
       f x ∷ (map f xs ++ map f ys)
    ≡⟨ sym refl ⟩
       (f x ∷ map f xs) ++ map f ys
    ≡⟨ refl ⟩
       map f (x ∷ xs) ++ map f ys
    ∎

-- A.2) Demostrar que map conmuta con la composición:
map-∘ : {A B C : Set} {f : A → B} {g : B → C} {xs : List A}
       → map (g ∘ f) xs ≡ map g (map f xs)
map-∘ {A} {B} {C} {f} {g} {[]} = refl
    -- begin
    --     map (g ∘ f) []
    -- ≡⟨ refl ⟩
    --     []
    -- ≡⟨ sym refl ⟩ 
    --     map g []
    -- ≡⟨ cong (λ z -> map g z) (sym refl) ⟩
    --     map g (map f [])
    -- ∎ 
map-∘ {A} {B} {C} {f} {g} {x ∷ xs} = 
    begin
        map (g ∘ f) (x ∷ xs)
    ≡⟨ refl ⟩ 
        ((g ∘ f) x) ∷ (map (g ∘ f) xs)
    ≡⟨ refl ⟩ 
        g (f x) ∷ (map (g ∘ f) xs)
    ≡⟨ cong (λ z -> g (f x) ∷ z) (map-∘) ⟩ 
        g (f x) ∷ (map g (map f xs))
    ≡⟨ refl ⟩ 
        map g (f x ∷ (map f xs))
    ≡⟨ refl ⟩ 
        map g (map f (x ∷ xs))
    ∎

-- Definimos el siguiente predicado que se verifica si un elemento
-- aparece en una lista:

_∈_ : {A : Set} → A → List A → Set
x ∈ []       = ⊥
x ∈ (y ∷ ys) = (x ≡ y) ⊎ (x ∈ ys)

-- data _⊎_ (A : Set a) (B : Set b) : Set (a ⊔ b) where
--   inj₁ : (x : A) → A ⊎ B
--   inj₂ : (y : B) → A ⊎ B

-- A.3) Demostrar que si un elemento aparece en la concatenación de
-- dos listas, debe aparecer en alguna de ellas:
∈-++ : ∀ {A : Set} {z : A} {xs ys : List A}
       → z ∈ (xs ++ ys)
       → (z ∈ xs) ⊎ (z ∈ ys)
∈-++ {A} {z} {[]} {ys} zInConcat = inj₂ zInConcat
∈-++ {A} {z} {x ∷ xs} {ys} (inj₁ z≡x ) = inj₁ (inj₁ z≡x)
∈-++ {A} {z} {x ∷ xs} {ys} (inj₂ zInConcat) with ∈-++ {xs = xs} (zInConcat)
... | inj₁ z∈xs = inj₁ (inj₂ z∈xs)
... | inj₂ z∈ys = inj₂ z∈ys

-- A.4) Demostrar que si un elemento z aparece en una lista xs,
-- su imagen (f z) aparece en (map f xs):
∈-map : ∀ {A B : Set} {f : A → B} {z : A} {xs : List A}
        → z ∈ xs
        → f z ∈ map f xs
∈-map {A} {B} {f} {z} {[]} () 
∈-map {A} {B} {f} {z} {x ∷ xs} (inj₁ z≡x) = inj₁ (cong f z≡x)
∈-map {A} {B} {f} {z} {x ∷ xs} (inj₂ zInXs) = inj₂ (∈-map {xs = xs} zInXs)

-- Definimos el siguiente predicado que se verifica si todos los
-- elementos de una lista son iguales:

todos-iguales : {A : Set} → List A → Set
todos-iguales []             = ⊤
todos-iguales (x ∷ [])       = ⊤
todos-iguales (x ∷ (y ∷ ys)) = (x ≡ y) × todos-iguales (y ∷ ys)

-- A.5) Demostrar:
todos-iguales-map : {A B : Set} {f : A → B} {xs : List A}
                  → todos-iguales xs
                  → todos-iguales (map f xs)
todos-iguales-map {A} {B} {f} {[]} todosIgualesListaVacio = todosIgualesListaVacio
todos-iguales-map {A} {B} {f} {x ∷ []} todosIgualesListaVacio = todosIgualesListaVacio
todos-iguales-map {A} {B} {f} {x ∷ (y ∷ ys)} (x≡y , todosIgualesy∷ys) = ((cong f x≡y) , todos-iguales-map todosIgualesy∷ys)

-- Parte B --

-- Definimos siguiente el tipo de las equivalencias de tipos.
--
-- Nota: estrictamente hablando, usamos la condición que afirma
-- que la función "to" tiene una quasi-inversa y no que es una
-- equivalencia.

record _≃_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : (a : A) → from (to a) ≡ a
    to∘from : (b : B) → to (from b) ≡ b

-- B.1) Demostrar que la equivalencia de tipos es reflexiva, simétrica y transitiva:

id : {A : Set} -> A -> A
id x = x

≃-refl : ∀ {A} → A ≃ A
_≃_.to (≃-refl {A}) = id
_≃_.from (≃-refl {A}) = id
_≃_.from∘to (≃-refl {A}) = (λ a -> refl)
_≃_.to∘from (≃-refl {A}) = (λ a -> refl) 

≃-sym : ∀ {A B} → A ≃ B → B ≃ A
_≃_.to (≃-sym aEquivB) = _≃_.from aEquivB
_≃_.from (≃-sym aEquivB) = _≃_.to aEquivB
_≃_.from∘to (≃-sym aEquivB) = (λ a -> (_≃_.to∘from aEquivB) a)
_≃_.to∘from (≃-sym aEquivB) = (λ a -> (_≃_.from∘to aEquivB) a)

≃-trans : ∀ {A B C} → A ≃ B → B ≃ C → A ≃ C
_≃_.to      (≃-trans A≃B B≃C) = (_≃_.to B≃C ∘ _≃_.to A≃B)
_≃_.from    (≃-trans A≃B B≃C) = (_≃_.from A≃B ∘ _≃_.from B≃C)
_≃_.from∘to (≃-trans A≃B B≃C) = (λ a → trans (cong (_≃_.from A≃B) ((_≃_.from∘to B≃C) (_≃_.to A≃B a))) (_≃_.from∘to A≃B a))
_≃_.to∘from (≃-trans A≃B B≃C) = (λ c -> trans (cong (_≃_.to B≃C) ((_≃_.to∘from A≃B) (_≃_.from B≃C c))) (_≃_.to∘from B≃C c))

-- B.2) Demostrar que el producto de tipos es conmutativo, asociativo,
-- y que ⊤ es el elemento neutro:

invert : {A B : Set} -> (A × B) -> (B × A)
invert (a , b) = (b , a)

×-comm : {A B : Set} → (A × B) ≃ (B × A)
_≃_.to ×-comm = invert
_≃_.from ×-comm = invert
_≃_.from∘to ×-comm = (λ (a , b) -> refl) 
_≃_.to∘from ×-comm = (λ (a , b) -> refl)

invert-order-× : {A B C : Set} -> (A × (B × C)) -> ((A × B) × C)
invert-order-× (a , (b , c)) = ((a , b) , c)

×-assoc : {A B C : Set} → (A × (B × C)) ≃ ((A × B) × C)
_≃_.to ×-assoc = (λ (a , (b , c)) -> ((a , b) , c))
_≃_.from ×-assoc = (λ ((a , b) , c) -> (a , (b , c)))
_≃_.from∘to ×-assoc = (λ (a , (b , c)) -> refl )
_≃_.to∘from ×-assoc = (λ ((a , b) , c) -> refl )

×-⊤-neut : {A : Set} → (A × ⊤) ≃ A
×-⊤-neut ._≃_.to = (λ (a , tt) -> a)
×-⊤-neut ._≃_.from = (λ a -> (a , tt))
×-⊤-neut ._≃_.from∘to = (λ (a , tt) -> refl)
×-⊤-neut ._≃_.to∘from = (λ a -> refl)

-- B.3) Demostrar que la suma de tipos es conmutativa, asociativa,
-- y que ⊥ es el elemento neutro:

⊎-comm : {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
⊎-comm ._≃_.to = λ {(inj₁ a) -> inj₂ a ; (inj₂ b) -> inj₁ b}
⊎-comm ._≃_.from = λ {(inj₁ b) -> inj₂ b ; (inj₂ a) -> inj₁ a}
⊎-comm ._≃_.from∘to = λ {(inj₁ a) -> refl ; (inj₂ b) -> refl }
⊎-comm ._≃_.to∘from = λ {(inj₁ b) -> refl ; (inj₂ a) -> refl }

⊎-assoc : {A B C : Set} → (A ⊎ (B ⊎ C)) ≃ ((A ⊎ B) ⊎ C)
⊎-assoc ._≃_.to = λ {(inj₁ a) -> (inj₁ (inj₁ a)) ; (inj₂ (inj₁ b)) -> inj₁ (inj₂ b)  ; (inj₂ (inj₂ c)) -> inj₂ c}
⊎-assoc ._≃_.from = λ {(inj₁ (inj₁ a)) -> inj₁ a ; (inj₁ (inj₂ b)) -> inj₂ (inj₁ b)  ; (inj₂ c) -> inj₂ (inj₂ c)} 
⊎-assoc ._≃_.from∘to = λ {(inj₁ a) -> refl ; (inj₂ (inj₁ b)) -> refl  ; (inj₂ (inj₂ c)) -> refl }
⊎-assoc ._≃_.to∘from = λ {(inj₁ (inj₁ a)) -> refl ; (inj₁ (inj₂ b)) -> refl ; (inj₂ c) -> refl } 

⊎-⊥-neut : {A : Set} → (A ⊎ ⊥) ≃ A
⊎-⊥-neut ._≃_.to = λ { (inj₁ a) -> a }
⊎-⊥-neut ._≃_.from = λ a -> inj₁ a
⊎-⊥-neut ._≃_.from∘to = λ { (inj₁ a) -> refl }
⊎-⊥-neut ._≃_.to∘from = λ a -> refl

-- B.5) Demostrar las siguientes "leyes exponenciales".
--
-- Nota:
-- Si leemos ⊥     como el cero 0,
--           ⊤     como el uno 1,
--           A ⊎ B como la suma A + B,
--           A × B como el producto A ∙ B,
--         y A → B como la potencia B ^ A,
-- las leyes dicen que:
--   A^0       = 1
--   A^1       = A
--   C^(A + B) = C^A ∙ C^B
--   C^(A ∙ B) = (C^B)^A

ExtensionalidadFuncional : Set₁
ExtensionalidadFuncional =
  {A : Set} {B : A → Set} {f g : (a : A) → B a}
  → ((a : A) → f a ≡ g a)
  → f ≡ g

postulate extensionalidad-funcional : ExtensionalidadFuncional


exp-cero : {A : Set} → (⊥ → A) ≃ ⊤
-- uso la notacion con pattern matching directo ahi
exp-cero ._≃_.to _ = tt
exp-cero ._≃_.from tt = λ x → ⊥-elim x
exp-cero ._≃_.from∘to f = extensionalidad-funcional (λ x → ⊥-elim x)
exp-cero ._≃_.to∘from = λ { tt -> refl }

exp-uno : {A : Set} → (⊤ → A) ≃ A
exp-uno ._≃_.to ttToA = ttToA tt
exp-uno ._≃_.from a = λ tt -> a
exp-uno ._≃_.from∘to = λ ttToA -> refl
exp-uno ._≃_.to∘from = λ a -> refl


exp-suma-to : {A B C : Set} → ((A ⊎ B) → C) → (A → C) × (B → C)
exp-suma-to aUnionBToC = (λ a → aUnionBToC (inj₁ a)) , (λ b → aUnionBToC (inj₂ b))

exp-suma-from : {A B C : Set} → ((A → C) × (B → C)) → ((A ⊎ B) → C)
exp-suma-from (aToC , bToC) = λ { (inj₁ a) → aToC a ; (inj₂ b) → bToC b }

aux1 : {A B C : Set} -> 
    (aUnionBToC : A ⊎ B -> C) -> (aUnionB : A ⊎ B) ->
    exp-suma-from (exp-suma-to aUnionBToC) aUnionB ≡ aUnionBToC aUnionB
aux1 aUnionBToC (inj₁ a) = refl
aux1 aUnionBToC (inj₂ b) = refl

-- aux1 : {A B C : Set} -> 
--     (aUnionBToC : A ⊎ B -> C) -> (aUnionB : A ⊎ B) ->
--     exp-suma-from (exp-suma-to aUnionBToC) aUnionB ≡ aUnionBToC aUnionB
-- aux1 aUnionBToC (inj₁ a) = refl
-- aux1 aUnionBToC (inj₂ b) = refl


exp-suma : {A B C : Set} → ((A ⊎ B) → C) ≃ ((A → C) × (B → C))
exp-suma ._≃_.to = exp-suma-to
exp-suma ._≃_.from = exp-suma-from
exp-suma ._≃_.from∘to aUnionBToC    = extensionalidad-funcional (aux1 aUnionBToC)
exp-suma ._≃_.to∘from (aToC , bToC) = refl

exp-producto : {A B C : Set} → ((A × B) → C) ≃ (A → B → C)
exp-producto ._≃_.to a,bToC = (λ a -> λ b -> a,bToC (a , b))
exp-producto ._≃_.from abToC = (λ (a , b) -> abToC a b)
exp-producto ._≃_.from∘to = (λ a,bToC -> refl)
exp-producto ._≃_.to∘from = (λ abToC -> refl)

-- B.5) Demostrar la generalización dependiente:

exp-producto-dep : {A : Set} {B : A → Set} {C : (a : A) → B a → Set}
                          → ((p : Σ[ a ∈ A ] B a) → C (proj₁ p) (proj₂ p))
                            ≃
                            ((a : A) (b : B a) → C a b)
exp-producto-dep ._≃_.to pToC = (λ a -> λ b -> pToC (a , b))
exp-producto-dep ._≃_.from abToC = (λ (a , b) -> abToC a b )
exp-producto-dep ._≃_.from∘to pToC = refl
exp-producto-dep ._≃_.to∘from abToC = refl

-- Parte C --

-- En este ejercicio vamos a demostrar que un compilador
-- minimalista es correcto.

-- Una expresión aritmética es una constante o la suma de dos expresiones:

data Expr : Set where
  e-const : ℕ → Expr
  e-add   : Expr → Expr → Expr

-- Definimos una función para evaluar una expresión aritmética:

eval : Expr → ℕ
eval (e-const n)   = n
eval (e-add e₁ e₂) = eval e₁ + eval e₂

-- Definimos una máquina de pila con 2 instrucciones,
-- una para meter un elemento en la pila y otra para
-- sumar los dos elementos del tope de la pila. Si no
-- argumentos suficientes, la instrucción no tiene efecto.

data Instr : Set where
  i-push : ℕ → Instr
  i-add  : Instr

-- Un programa es una lista de instrucciones.
-- Definimos una función para ejecutar un programa
-- sobre una pila de números naturales:

run : List Instr → List ℕ → List ℕ
run []                stack             = stack
run (i-push n ∷ prog) stack             = run prog (n ∷ stack)
run (i-add ∷ prog)    []                = run prog []          -- (No hay argumentos suficientes).
run (i-add ∷ prog)    (n ∷ [])          = run prog (n ∷ [])    -- (No hay argumentos suficientes).
run (i-add ∷ prog)    (m ∷ (n ∷ stack)) = run prog ((n + m) ∷ stack)

-- Definimos el compilador como una función que recibe
-- una expresión aritmética y la convierte en una lista
-- de instrucciones:

compile : Expr → List Instr
compile (e-const n)   = i-push n ∷ []
compile (e-add e₁ e₂) = (compile e₁ ++ compile e₂) ++ (i-add ∷ [])

-- Demostrar que el compilador es correcto:

lema-run-++ : {xs ys : List Instr} {stack : List ℕ} -> run (xs ++ ys) stack ≡ run xs (run ys stack) 
lema-run-++ = ?  

lema-run-compile : {e b : Expr} -> run (compile e) (eval b ∷ []) ≡ (eval e + eval b) ∷ []
lema-run-compile {e-const x} {b} = ?
lema-run-compile {e-add y z} {b} = ?

compile-correct : {e : Expr}
                → run (compile e) [] ≡ eval e ∷ []
compile-correct {e-const x} = refl
compile-correct {e-add e e₁} = 
    begin 
        run (compile (e-add e e₁)) []
    ≡⟨ refl ⟩ 
        run ((compile e ++ compile e₁) ++ (i-add ∷ [])) []
    ≡⟨ lema-run-++ {xs = (compile e ++ compile e₁)} {ys = (i-add ∷ [])} {stack = []}⟩ 
        run (compile e ++ compile e₁) (run (i-add ∷ []) [])
    ≡⟨ cong (λ z -> run (compile e ++ compile e₁) z ) refl ⟩ 
        run (compile e ++ compile e₁) []
    ≡⟨ lema-run-++ {xs = compile e} {ys = compile e₁} {stack = []} ⟩ 
        run (compile e) (run (compile e₁) [])
    ≡⟨ cong (λ z -> run (compile e) z ) (compile-correct {e₁}) ⟩ 
        run (compile e) (eval e₁ ∷ [])
    ≡⟨ lema-run-compile {e} {e₁} ⟩ 
        (eval e + eval e₁) ∷ []
    ≡⟨ sym refl ⟩ 
        eval (e-add e e₁) ∷ []
    ∎

