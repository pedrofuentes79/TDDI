-- Ej1. Definir habitantes de los siguientes tipos
flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f b a = f a b

compose : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
compose bToC aToB a = bToC (aToB a)

-- Desde el punto de vista computacional, flip significa aplicar una funcion en el orden inverso de los parametros
-- compose significa componer dos funciones en una sola.

-- Desde el punto de vista logico compose representa la transitividad de la implicacion!
-- y flip no se :D

--Ej 2 booleanos
--2a defininir el principio de eliminiacion con pattern matching

data Bool : Set where
    false : Bool
    true : Bool

recBool : {C : Set} -> C -> C -> Bool -> C
recBool _ caseTrue true = caseTrue
recBool caseFalse _ false = caseFalse

not : Bool -> Bool
not = recBool true false

--Ej 3 productos

data _x_ (A B : Set) : Set where
    _,_ : A -> B -> A x B

recProduct : {A B C : Set} -> (A -> B -> C) -> A x B -> C
recProduct f (a , b) = f a b 

-- eliminacion dependiente
-- P es un tipo "dinamico" que depende de los tipos que recibe
-- Es decir: la salida podria ser un bool (tomemos A=String y B=String) con a='123' y b='123'
-- pero podria ser un natural si a='asd' y b='qwerty'.
{-- 
Entonces definimos el tipo P: (AxB->Set).
Y la funcion f que recibimos ahora va a tener como tipo de salida lo que sea que nos diga P.
Es decir, P (a , b) donde a y b son habitantes del tipo A y B respectivamente
Luego, recibimos el producto (de tipo p : A x B)
Y nuestra salida va a ser de tipo P p. 
--}
elimDependiente : {A B : Set} {P : A x B -> Set }-> 
                  ((a : A) -> (b : B) -> (P (a , b))) ->
                  (p : A x B) -> P p
elimDependiente f (a , b) = f a b

-- === DEMOSTRACIONES DE PROPIEDADES ===
-- Recordar que demostrar ese tipo es dar un habitante. En este caso es fst y snd

π₁ : {A B : Set} -> A x B -> A
π₁ = recProduct (λ a _ -> a)

π₂ : {A B : Set} -> A x B -> B
π₂ = recProduct (λ _ b -> b)

curryProduct : {A B : Set} {P : A x B -> Set} ->
                ((p : A x B) -> (P p)) ->
                ((a : A) -> (b : B) -> (P (a , b)))

--Esto es porque la funcion f espera un producto.
--Nosotros recibimos dos separados y devolvemos la aplicacion de f
curryProduct f a b = f (a , b)

-- lo mismo pero al reves
uncurryProduct : {A B : Set} {P : A x B -> Set} ->
                ((a : A) -> (b : B) -> (P (a , b))) ->
                ((p : A x B) -> (P p))
uncurryProduct f (a , b) = f a b

--Si el tipo P de retorno no dependiese de (AxB) seria un tipo fijo. Podria quedar de esta manera
curryProductFijo : {A B C : Set} -> (A x B -> C) -> (A -> B -> C)
curryProductFijo f a b = f (a , b)

--Ej 4
data ⊥ : Set where

-- tuve que pedir ayuda para este... No se me ocurrio que simplemente no hay manera de pattern matchearlo
-- () representa el pattern matching vacio
⊥-elim : {C : Set} -> ⊥ -> C
⊥-elim ()

-- Demostrar sin pattern matching que (A -> ⊥) -> A -> B. Usar el principio de eliminacion si es necesario.
absurdo : {A B : Set} -> (A -> ⊥) -> A -> B
absurdo aImplicaBottom a = ⊥-elim (aImplicaBottom a)
-- Decir que "a implica bottom" es que si vale A, puedo derivar un absurdo (en este caso, cualquier B)
-- Entonces, vemos que a partir de un absurdo podemos derivar cualquier cosa. Y esto es lo que nos pedian.

-- Ej 5
-- Tipo inductivo unitario
data ⊤ : Set where
    tt : ⊤

indUnit : { C : ⊤ -> Set } -> C tt -> ( x : ⊤ ) -> C x
{--Hacemos pattern matching. Como tt es la unica posibilidad para el tipo ⊤ lo ponemos ahi
Luego, nos piden devolver algo de tipo C x (osea Set)
Como lo que recibimos es de tipo "C tt" y C recibe ⊤ y devuelve Set, 
simplemente devolvemos eso que nos dieron
--}
indUnit c_tt tt = c_tt

--Ej6 Sumas dependientes

data Σ (A : Set) (B : A -> Set) : Set where
    _,_ : (a : A) -> B a -> Σ A B

elimDependienteΣ : { A B : Set } { P : ? -> Set } -> 
                ((a : A) -> ? -> ?) ->
                (p : P) -> ?

elimDependienteΣ f a = ?