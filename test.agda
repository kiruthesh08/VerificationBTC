
module test  where


test :  (A B : Set) → A → B → A
test = λ A B a b → a

data _∨_ (A B : Set) : Set where -- _x_ notation
  ∨-intro₀ : A → A ∨ B -- disjuntion 
  ∨-intro₁ : B → A ∨ B

data Bool : Set where
  true  : Bool
  false : Bool

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

data _∧_ (A B : Set) : Set where
  ∧-introduction : A → B → A ∧ B


data List (A : Set) : Set where
  [] : List A
  cons  : A → List A → List A


data ListI : Set → Set₁ where
  zero  : {A : Set} → ListI A
  _∷_ : {A : Set} → A → ListI A → ListI A





