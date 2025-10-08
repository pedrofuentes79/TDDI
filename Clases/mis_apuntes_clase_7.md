Grupo abeliano. 
Vale la conmutatividad (op a b = op b a), y otras propiedades.

GrupoAbeliano : Set_1
GrupoAbeliano = damos 4 cosas. 
1) el tipo de los elementos. 
    1.5) si queremos ser mas estricto, habría que pedir que A sea un Set. Pero omitimos esto.
2) una operacion que dado dos A devuelve otra. 
3) un elemento neutro
4) hay una inversa?

- Todos los habitantes de este tipo son 4-uplas de esas cosas.
- Es Set_1 porque es un tipo "de tipos"?

--- o ---

-- Olvidamos la parte anterior. Es una def. mas de "teoria de tipos". Usamos un record que es mas lindo

record AnilloConmutativo : Set_1 where
    field
        R : Set 
        _+_ : R -> R -> R
        \b0 -- el elemento neutro de la suma
        -_ 
        _*_
        \b1 -- el elemento neutro de la multiplicacion
        ---
        +-comm
        +-assoc
        +-neutro-izq : { x : R } -> \b0 + x \equiv x

        *-assoc, *-comm, *-neut-izq
        *-+-distribuye-izq : {x y z : R} -> (x + y) * z \equiv x * z + y * z


y ahora probamos cositas

anillo-enteros : AnilloConmutativo
anillo-enteros = ? -- aca le mandas C-c C-c y te splitea todo para que completes cada uno

--- o ---


Para usar un record de manera mas comoda, usamos
module TeoriaDeAnillos (A : AnilloConmutativo) where
    openAnilloConmutativo A

    +-neut-r : (x : R) -> x + \b0 \equiv x
    +-neut-r = ?
    
    
test = TeoriaDeAnillos.+-neut-r -- esto me da el tipo (verbose) que quiero

----------------------------------------------------   o    ---------------------------------------------------- 

SyntheticDifferentialGeometry (anillo conmutativo)

    infinitesimal : R -> Set
    infinitesimal e = e * e \equiv \b0

    esPendiente0: (R -> R) -> R -> Set
    esPendiente0 f k = (i : R) -> infinitesimal i -> f i  \equiv   f \b0 + k * i

    postulate Kock-Lawvere: para toda funcion de R en R, existe un k tal que k esPendiente0 de f.

    pendiente0 f = π_1 (Kock-Lawvere f)
    porque KL te daba el k que cumplia.

    