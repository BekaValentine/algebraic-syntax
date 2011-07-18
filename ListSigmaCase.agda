open import Data.Nat
open import Data.Unit

module ListSigmaCase where



infixr 4 _::_
data List : Set where
  [] : List
  _::_ : ℕ → List → List



list-case : ∀ {X : Set} → List → X → (ℕ → List → X) → X
list-case [] z f = z
list-case (x :: xs) z f = f x xs

isList : List → Set
isList _ = ⊤

p : (xs : List) → isList xs
p xs = list-case xs tt (λ _ _ → tt)

list-spec : (f : List → Set)
          → f []
          → (∀ {x xs} → f xs → f (x :: xs))
          → (∀ {xs} → f xs)
list-spec f z c {[]} = z
list-spec f z c {x :: xs} = c {x} {xs} (list-spec f z c {xs})

list-ind : (P : List → Set)
         → P []
         → (∀ x xs → P xs → P (x :: xs))
         → ∀ xs → P xs