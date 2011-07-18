{-# OPTIONS --universe-polymorphism #-}

open import Data.Empty
open import Data.Fin
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Vec
open import Function
open import Relation.Binary.Core

module Map where




case : ∀ {X Y : Set} {n : ℕ}
      → Vec X n
      → Y
      → (∀ {n} → X → Vec X n → Y)
      → Y
case [] z f = z
case (x ∷ xs) z f = f x xs


infixr 9 _↔_
_↔_ : ∀ {n} → Set n → Set n → Set n
X ↔ Y = (X → Y) × (Y → X)

infixr 9 _≅_
_≅_ : ∀ {n} → Set n → Set n → Set n
X ≅ Y = Σ[ f ∶ (X → Y) ]
         (Σ[ b ∶ (Y → X) ]
           (∀ x → x ≡ b (f x)) × (∀ y → y ≡ f (b y)))

-- A stupid derivation

nil : ∀ {X : Set} {n : ℕ} → Vec X n → Set
nil [] = ⊤
nil (x ∷ xs) = ⊥

empty-theorem : Σ[ empty ∶ (∀ {X : Set} {n : ℕ} → Vec X n → Set) ]
                 ((X : Set) (n : ℕ) (xs : Vec X n)
                  → nil xs ↔ empty xs)
empty-theorem = (λ {X} {n} → empty {X} {n}) , p
  where empty : ∀ {X : Set} {n : ℕ} → Vec X n → Set
        empty [] = ⊤
        empty (x ∷ xs) = ⊥
        
        p : (X : Set) (n : ℕ) (xs : Vec X n)
            → nil xs ↔ empty xs
        p X zero [] = pl , pr
          where pl : nil {X} [] → empty {X} []
                pl n[] = n[]
                -- need an empty [] but all we have is a nil []
                -- however, empty [] is as of yet undefined
                -- so define it to be the same as nil []: ⊤
                
                pr : empty {X} [] → nil {X} []
                pr e[] = e[]
                -- having defined empty [] to be ⊤
                -- we can give a nil [] == ⊤ by giving back
                -- the empty [] argument
        
        p X (suc n) (x ∷ xs) = pl , pr
          where pl : nil {X} (x ∷ xs) → empty {X} (x ∷ xs)
                pl n∷ = n∷
                -- we need some empty (x ∷ xs) but all we have
                -- is a nil (x ∷ xs). empty (x ∷ xs) is currently undefined
                -- however, so define it to be the same as nil (x ∷ xs)
                -- and return n∷
                
                pr : empty {X} (x ∷ xs) → nil {X} (x ∷ xs)
                pr e∷ = e∷
                -- similarly we return e∷
-- Note that the structure of this derivation allows us to simplify greatly:
--   empty-theorem = _ , λ _ _ _ → id , id
-- the definition of empty follows inexorably from the proof, and so can be deduced!
-- however, without a better understanding of this kind of derivation,
-- this is not possible in general. the best we can do so far is have (_ , p)-like witnesses

empty : ∀ {X : Set} {n : ℕ} → Vec X n → Set
empty = proj₁ empty-theorem


veccase : ∀ {X : Set _} {Y : Set _}
        → Y
        → (∀ {n} → X → Vec X n → Y)
        → ∀ {n} → Vec X n → Y
veccase z f [] = z
veccase z f (x ∷ xs) = f x xs

refine : ∀ {m n}
       → (X : Set m)
       → (P : X → Set n)
       → Set _
refine = Σ
syntax refine A (λ x → B) = x ∶ A ⟨ B ⟩

vecsplit : ∀ {X : Set _} {Y : Set _}
         → (P : ∀ {X : Set _} {n} → Vec X n → Y → Set)

         → Σ[ y ∶ Y ]
              (P {X} [] y)

         → Σ[ f ∶ (∀ {X : Set _} {n} → X → Vec X n → Y) ]
              (∀ {n} x (xs : Vec X n) → P (x ∷ xs) (f x xs))

         → Σ[ f ∶ (∀ {X : Set _} {n} → Vec X n → Y) ]
              (∀ {n} (xs : Vec X n) → P xs (f xs))

vecsplit P (fz , pz) (fs , ps) = (λ {X} → veccase {X} fz fs) ,
                                 (λ {n} → pcomb {n})
  where pcomb : ∀ {n} (xs : Vec _ n) → P xs (veccase fz fs xs)
        pcomb [] = pz
        pcomb (x ∷ xs) = ps x xs

bicond-⊤ : Σ[ X ∶ Set ] (⊤ ↔ X)
bicond-⊤ = ⊤ , _

--bicond-⊤-vec : Σ[ f ∶ ∀ {X : Set} {n} → Vec X n → Set ] (∀ {n} (

vector : ∀ {X : Set} {n} → Vec X n → Set
vector _ = ⊤

fp : ∀ {X : Set} → Σ[ f ∶ (∀ {X : Set} {n} → Vec X n → Set) ] (∀ {n} (xs : Vec X n) → vector xs ↔ f xs)
fp {X} = vecsplit (λ xs fxs → vector xs ↔ fxs)
                  bicond-⊤
                  ((λ x x' → ⊤) , (λ x xs → id , id))

mapR-theorem : Σ[ mapR ∶ (∀ {X Y : Set} {n : ℕ}
                          → (X → Y → Set)  -- (X × Y → Set)
                          → Vec X n → Vec Y n → Set) ]  -- (Vec X n × Vec Y n → Set)
                 ((X Y : Set) (n : ℕ) (f : X → Y → Set) (xs : Vec X n) (ys : Vec Y n)
                    → mapR f xs ys ↔ (∀ i → f (lookup i xs) (lookup i ys)))
mapR-theorem = _ , p
  where mapR : ∀ {X Y : Set} {n : ℕ}
               → (X → Y → Set)
               → (xs : Vec X n) → (ys : Vec Y n) → Set
        mapR f [] [] = ⊤
        mapR f (x ∷ xs) (y ∷ ys) = f x y × mapR f xs ys
        
        p : (X Y : Set) (n : ℕ) (f : X → Y → Set) (xs : Vec X n) (ys : Vec Y n)
            → mapR f xs ys ↔ ((i : Fin n) → f (lookup i xs) (lookup i ys))
        p _ _ zero f [] [] = nnl , nnr
          where nnl : mapR f [] [] → (i : Fin zero) → f (lookup i []) (lookup i [])
                nnl mfnn = λ ()
                -- Here we can see that the type ∀ i → f (lookup i []) (lookup i [])
                -- is actually inhabited, namely, only by the empty function
                -- and thus is ≅ ⊤
                
                nnr : ((i : Fin zero) → f (lookup i []) (lookup i [])) → mapR f [] []
                nnr g = tt
                -- since ∀ i → f (lookup i []) (lookup i []) ≅ ⊤
                -- and since functions are total, mapR f [] [] ≅ ⊤
                -- and we must be able to give a definition for nnr that is non-empty
                -- but what to choose as a return value?
                -- well, map f [] [] is as of yet unspecified
                -- so lets choose the simplest type ≅ ⊤: ⊤
                
        p X Y (suc n) f (x ∷ xs) (y ∷ ys) = ccl , ccr
          where ccl : mapR f (x ∷ xs) (y ∷ ys) → (i : Fin (suc n)) → f (lookup i (x ∷ xs)) (lookup i (y ∷ ys))
                ccl pr zero = proj₁ pr
                -- need a proof of f x y, and we have an as of yet unspecified type map f (x ∷ xs) (y ∷ ys)
                -- so lets choose a definition of map f (x ∷ xs) (y ∷ ys) that gives us what we need
                -- at least partially: we'll make it a pair so that we have more info for the second case of ccl
                
                ccl pr (suc i) = proj₁ (p X Y n f xs ys) (proj₂ pr) i
                -- we can use recursively generate the needed proof
                -- where r is, we needed a map f xs ys, and we have
                -- a partially unspecified type: the second half of map!
                
                ccr : ((i : Fin (suc n)) → f (lookup i (x ∷ xs)) (lookup i (y ∷ ys))) → mapR f (x ∷ xs) (y ∷ ys)
                ccr g = g zero , proj₂ (p X Y n f xs ys) (λ i′ → g (suc i′))
                -- again recursively generate the needed proof

mapR : ∀ {X Y : Set} {n : ℕ}
      → (X → Y → Set)
      → (xs : Vec X n) → (ys : Vec Y n) → Set
mapR = proj₁ mapR-theorem



{-
  given that
  
    P empty = (X : Set) → (n : ℕ) → (xs : Vec X n) → nil xs ↔ empty xs
  
  notice that the type of nil and the type of empty are the same
  hence what we're saying is that nil ⇔ empty

  for mapR:

    P mapR = (X Y : Set) (n : ℕ) (f : X → Y → Set) (xs : Vec X n) (ys : Vec Y n)
             → mapR f xs ys ↔ (∀ i → f (lookup i xs) (lookup i ys))
    p : P mapR
    
  what is the F such that
    
    P mapR == (X Y : Set) (n : ℕ) (f : X → Y → Set) (xs : Vec X n) (ys : Vec Y n)
              → mapR f xs ys ↔ F f xs ys
  
  Obviously just:

    F : (X → Y → Set) → (xs : Vec X n) → (ys : Vec Y n) → Set
    F f xs ys = ∀ i → f (lookup i xs) (lookup i ys)

  but consider the cases of F:

    F f [] [] = ∀ (i : Fin zero) → f (lookup i []) (lookup i [])
  
  but Fin zero ≅ ⊥, so the only inhabitant is
  
    g : F f [] [] = ∀ (i : Fin zero) → f (lookup i []) (lookup i [])
    g ()

  since there's an inhabitant, the corresponding mapR case must be provable
  so it must have a non-empty type, so we can choose a type that's trivial to prove: ⊤
  
  now consider

    F f (x ∷ xs) (y ∷ ys) = ∀ (i : Fin (suc .n)) → f (lookup i (x ∷ xs)) (lookup i (y ∷ ys))
  
    h : F f (x ∷ xs) (y ∷ ys) = ∀ (i : Fin (suc .n)) → f (lookup i (x ∷ xs)) (lookup i (y ∷ ys))
    h zero = {! f (lookup zero (x ∷ xs)) (lookup zero (y ∷ ys)) !}
           = {! f x y !}
    h (suc i) = {! f (lookup (suc i) (x ∷ xs)) (lookup (suc i) (y ∷ ys)) !}
              = {! f (lookup i xs) (lookup i ys) !}1
  
  it seems like what we want to be able to say is that empty proof functions map to ⊤
  and recursive proof functions map to structurally similar recursive functions
    g = λ () ~> ⊤
    h = finCase (? : f x y) (? : f (lookup i xs) (lookup i ys)) ~> f x y × mapR f xs ys
  
-}