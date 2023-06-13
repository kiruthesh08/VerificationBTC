module demo1A where

--simple data type bools


data Bool : Set where
  true : Bool
  false : Bool      -- closely to haskell, set type for bool data type, types have type

-- data type not



not : Bool → Bool -- arrow syntax is backslash to
not true = false 
not false = true  -- to get a hole we use ? to go into Agda more specifically 

-- right click in hole and use refine


-- define if

if_then_else : {A : Set}→ Bool → A → A → A    -- A:set is used to define a as set 
if true then x else y = x
if false then x else y = y  -- used case split

-- inductive definition natural numbers

data Nat : Set where
  zero : Nat
  suc : Nat → Nat    -- suc takes in param as its type

add : Nat → Nat → Nat
add zero y = y     -- add x y = ? then use case split before split enter value in {x}
add (suc y) y' = suc(add y  y') -- works but we want to define + symbol
_+_ : Nat → Nat → Nat
zero + b = b 
suc a + b = suc (a + b)  -- case with b in {}

-- test new + symbol

low = suc zero
high = low + (low + low) -- evaluate using ctrl c and ctrl n


-- lists

data List (A : Set) : Set where  -- a : set denotes type param to list data type 
  Nil : List A
  Cons : A → List A → List A

-- define list operations length map and concat

length : {A : Set} → List A → Nat
length Nil = zero
length (Cons y y') = suc(length y')   -- help idk how he got this condition




map : {A B : Set} → (A → B) → List A → List B  -- grouped mutliple param in {}
map f Nil = Nil
map f (Cons y y') = Cons (f y) (map f y')



concat : {A : Set} → List A → List A → List A
concat Nil m = m  -- concat l m use l in {} followed by case, then input m 
concat (Cons x l) m = Cons x (concat l m) 

-- vectors


data Vector ( A : Set) : Nat → Set where
 Q : Vector A zero
 W  : {n : Nat} → A → Vector A n → Vector A (suc n)

-- to vector there exists a type param and a value param


-- redifine list function for vector 



vlength : {A : Set} → {n : Nat} → Vector A n → Nat
vlength {_}{n} v = n  -- why does it load now but not to vlength v = .n 13.00



vMap : {A B : Set} → {n : Nat} → (A → B) → Vector A n → Vector B n

vMap f Q = Q  -- use case on vMap f v = ? and in brackets enter v with case 
vMap f (W x v) = W (f x) (vMap f v) -- use auto and it solves for us

-- _ underscores denote placeholders

vConcat : {A : Set} → {n m  : Nat} → Vector A n → Vector A m → Vector A(n + m)
vConcat Q w = w  -- vConcat v w =?        user defindeed datatpes  in {v} then use case 
vConcat (W x v) w = W x (vConcat v w) -- use auto 



data False : Set where

postulate close : False



postulate noElem : fin 0

