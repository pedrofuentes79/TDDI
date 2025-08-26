data ℕ : Set where
    zero : ℕ
    suc : ℕ -> ℕ

infixl 60 _+_

_+_ : ℕ -> ℕ -> ℕ
zero  + m = m
suc n + m = suc (n + m)

indN : (C : ℕ -> Set) ->  --flia indexada
        C zero -> --caso zero
        ({n : ℕ} -> C n -> C (suc n)) ->  -- el caso inductivo (?
        (n : ℕ) -> --el natural en cuestion
        C n
indN C c0 cs zero    = c0
indN C c0 cs (suc n) = cs (indN C c0 cs n)

data _≡_ { A : Set } : (a b : A) -> Set where
    refl : (a : A) -> a ≡ a

-- literal el tipo que copiamos en la carpeta, es simple este.
-- el {a b : A} se puede poner explicito o no ( segun pablo)
sym : {A : Set} {a b : A} -> a ≡ b -> b ≡ a
sym (refl a) = (refl a)

trans : { A : Set } { a b c : A} -> a ≡ b -> b ≡ c ->  a ≡ c
-- siendo p y q dos caminos
trans (refl a) (refl a) = refl a

--cong...

--Demo de que la suma es asociativa

--
infixr 20 _≡⟨_⟩_
infixr 30 _■
_≡⟨_⟩_ : {A : Set} (a : A) -> {b : A} (p: a ≡ b) -> {c : A} a ≡ c­
_ ≡⟨ p ⟩ q = trans p q

_■ : { A : Set} ( a : A) -> a ≡ a
_ ■ = refl

+-assoc : {n m q : ℕ} -> n + (m + q) ≡ (n + m) + q
+-assoc {zero}  {m} {q} = 
    zero + (m + q)
≡ ⟨ refl ⟩ 
    (m + q)
≡ ⟨ refl ⟩ 
    (zero + m) + q
■

--qvq ((suc n) + m) + q = (suc n) + (m+q)
-- queda cong suc (+-assoc...)
+-assoc {suc n} {m} {q} = {!   !}

------------

_≤