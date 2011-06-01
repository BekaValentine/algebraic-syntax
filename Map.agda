open import Naturals
open import Functions
open import Logic
open import Relations

module Map where




data Vec (X : Set) : ℕ → Set where
  nil : Vec X zero
  _::_ : ∀ {n} → X → Vec X n → Vec X (suc n)

data Fin : ℕ → Set where
  fzero : ∀ {n} → Fin (suc n)
  fsuc : ∀ {n} → Fin n → Fin (suc n)

proj : ∀ {X n} → Vec X n → Fin n → X
proj nil ()
proj (x :: _) fzero = x
proj (x :: xs) (fsuc i) = proj xs i

map-theorem : ∃ (∀ {X Y n}
                 → (X → Y → Set) → Vec X n → Vec Y n
                 → Set)
                (λ map → (X Y : Set) (n : ℕ) (f : X → Y → Set) (xs : Vec X n) (ys : Vec Y n)
                       → map f xs ys ↔ ((i : Fin n) → f (proj xs i) (proj ys i)))
map-theorem = exists (λ {X} {Y} {n} → map {X} {Y} {n}) p
  where map : ∀ {X Y n}
              → (f : X → Y → Set) → (xs : Vec X n) → (ys : Vec Y n)
              → Set
        map f nil nil = ⊤
        map f (x :: xs) (y :: ys) = f x y ∧ map f xs ys
        
        p : (X Y : Set) (n : ℕ) (f : X → Y → Set) (xs : Vec X n) (ys : Vec Y n) → map f xs ys ↔ ((i : Fin n) → f (proj xs i) (proj ys i))
        p X Y zero f nil nil = nnl , nnr
          where nnl : map f nil nil → (i : Fin zero) → f (proj nil i) (proj nil i)
                nnl mfnn ()
                  where g : (i : Fin zero) → f (proj nil i) (proj nil i) 
                        g ()
                        -- Here we can see that the type (i : Fin zero) → f (proj nil i) (proj nil i)
                        -- is actually inhabited, namely, by the empty function
                
                nnr : ((i : Fin zero) → f (proj nil i) (proj nil i)) → map f nil nil
                nnr g = tt
                -- since (i : Fin zero) → f (proj nil i) (proj nil i) is inhabited,
                -- we must be able to give a definition for nnr that is non-empty
                -- but what to choose as a return value?
                -- well, map f nil nil is as of yet unspecified
                -- so lets choose the simplest type with with proofs: ⊤
                
        p X Y (suc n) f (x :: xs) (y :: ys) = ccl , ccr
          where ccl : map f (x :: xs) (y :: ys) → (i : Fin (suc n)) → f (proj (x :: xs) i) (proj (y :: ys) i)
                ccl (fxy , _) fzero = fxy
                -- need a proof of f x y, and we have an as of yet unspecified type map f (x :: xs) (y :: ys)
                -- so lets choose a definition of map f (x :: xs) (y :: ys) that gives us what we need
                -- at least partially: we'll make it a pair so that we have more info for the second case of ccl
                
                ccl (fxy , r) (fsuc i) = fst (p X Y n f xs ys) r i
                -- we can use recursively generate the needed proof
                -- where r is, we needed a map f xs ys, and we have
                -- a partially unspecified type: the second half of map!
                
                ccr : ((i : Fin (suc n)) → f (proj (x :: xs) i) (proj (y :: ys) i)) → map f (x :: xs) (y :: ys)
                ccr g = g fzero , snd (p X Y n f xs ys) (λ i′ → g (fsuc i′))
                -- again recursively generate the needed proof

map : ∀ {X Y n}
      → (f : X → Y → Set) → (xs : Vec X n) → (ys : Vec Y n)
      → Set
map = ∃-witness map-theorem