La idea de la clase es formalizar calculo lambda en agda!

BTy (Base type)
Ty :
    base : BTy -> Ty
    _=>_ : Ty -> Ty -> Ty

------ o -------
data Tm : Set where
    var : String -> Tm
    lam : String -> Tm -> Tm --lambda
    app : Tm -> Tm -> Tm

id = lam "x" (var "x")

Definir la sustitucion requiere que chequeemos captura. Se puede usar el decisor de la igualdad de strings para ver si dos variables son la misma.

Este camino es medio complejo. Tiene quilombos...

------ o -------
Este approach hace que los terminos que podamos escribir van a usar el sistema de tipos de agda para asegurarnos de que tipen

- Definicion de contexto: o es vacio o es la extension de un contexto (\_,,\_) con un tipo
- Define un predicado que determina si un tipo esta en un contexto
    - zero: el caso base, en el que el contexto que recibimos es (K ,, A). Luego A \in K.
    - suc


--ejs
K = \vacio ,, base 0 ,, base 0 => base 1

var0 : K \ni (base 0 => base 1)
var0 = zero

var1 : K \ni (base 0)
var1 = suc ?

------ o ------

Luego se define el "trinquete" que permite definir un juicio de tipado. Son o terminos o arboles de derivacion, lo que se prefiera interpretar. A mi me queda mas comodo un arbol de derivacion.
    - var
    - lam
    - app

Ej: para dar un \vacio \trinq A => A
lam (?)
aca, el hole es dar algo de tipo (\vacio ,, A \trinq A)
entonces ponemos
lam (var zero)

---- o ----
Renombres: una funcion que, a cada variable de un contexto la manda a una variable de otro contexto. Estas variables tienen que ser del mismo tipo. 

Dado un type y que ese type esta en Gamma, devuelve que ese type esta en Delta

renombrar (la funcion posta, la que hace el renombre)
renombrar {\Gamma \Delta A} -> Renombre \Gamma \Delta -> \Gamma \trinq A -> \Delta \trinq A
renombrar p (var x) = let x' = p x in var x'

-- esto no tipa!
renombrar p (lam M) = let M' = renombrar p M in ?
-- necesitamos una funcio auxiliar detallada abajo
renombrar p (lam M) = let M' = renombrar (shift p) M in lam M'

renombrar p (app M N) = let M' = renombrar p M
                            N' = renombrar p N
                        in app M' N'

shift: dados gamma, delta y A, un renombre de Gamma a delta, doy un renombre de (Gamma extendido con A) a (delta extendido con A) 
-- unifica varias cosas aca...
shift p (zero) = zero
shift p (suc q) = suc p q

------ o -------
Sustitución.

