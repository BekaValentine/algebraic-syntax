{-# OPTIONS --universe-polymorphism #-}

open import Naturals

module Functions where



id : ∀ {n} {X : Set n} → X → X
id x = x

const : ∀ {m n} {X : Set m} {Y : Set n} → X → Y → X
const x _ = x

const′ : ∀ {n} {X Y : Set n} → X → Y → X
const′ = const

const2 : ∀ {l m n} {X : Set l} {Y : Set m} {Z : Set n} → X → Y → Z → X
const2 x _ _ = x

const2′ : ∀ {n} {X Y Z : Set n} → X → Y → Z → X
const2′ = const2

infixl 12 _∘_
_∘_ : ∀ {l m n} {X : Set l} {Y : Set m} {Z : Set n} → (Y → Z) → (X → Y) → (X → Z)
(f ∘ g) x = f (g x)

infixl 12 _∘′_
_∘′_ : ∀ {n} {X Y Z : Set n} → (Y → Z) → (X → Y) → (X → Z)
_∘′_ = _∘_

_⟨_⟩_ : ∀ {l m n} {X : Set l} {Y : Set m} {Z : Set n} → X → (X → Y → Z) → Y → Z
x ⟨ f ⟩ y = f x y

flip : ∀ {l m n} {X : Set l} {Y : Set m} {Z : Set n} → (X → Y → Z) → (Y → X → Z)
flip f x y = f y x



infixr 11 _×_
infixr 0 _,_
{-
data _×_ {n} (X Y : Set n) : Set n where
  _,_ : X → Y → X × Y
-}
record _×_ {n} (X Y : Set n) : Set n where
  constructor _,_
  field
    fst : X
    snd : Y
    
fst : ∀ {n} {X Y : Set n} → X × Y → X
fst = _×_.fst

snd : ∀ {n} {X Y : Set n} → X × Y → Y
snd = _×_.snd

curry : ∀ {n} {X Y Z : Set n} → (X × Y → Z) → (X → Y → Z)
curry f x y = f (x , y)

uncurry : ∀ {n} {X Y Z : Set n} → (X → Y → Z) → (X × Y → Z)
uncurry f (x , y) = f x y

infixr 11 _▵_
_▵_ : ∀ {n} {X Y Y′ : Set n} → (X → Y) → (X → Y′) → (X → Y × Y′)
(f ▵ g ) x =  (f x , g x)

infixr 11 _×′_
_×′_ : ∀ {n} {X X′ Y Y′ : Set n} → (X → Y) → (X′ → Y′) → (X × X′ → Y × Y′)
(f ×′ g) (x , y) = (f x , g y)


infixr 10 _+_
data _+_ {n} (X Y : Set n) : Set n where
  inl : X → X + Y
  inr : Y → X + Y

infixr 10 _▿_
_▿_ : ∀ {n} {X X′ Y : Set n} → (X → Y) → (X′ → Y) → (X + X′ → Y)
(f ▿ g) (inl x) = f x
(f ▿ g) (inr y) = g y

infixr 10 _+′_
_+′_ : ∀ {n} {X X′ Y Y′ : Set n} → (X → Y) → (X′ → Y′) → (X + X′ → Y + Y′)
(f +′ g) (inl x) = inl (f x)
(f +′ g) (inr y) = inr (g y)



distl : ∀ {n} {X Y Z : Set n} → X × (Y + Z) → (X × Y) + (X × Z)
distl (x , inl y) = inl (x , y)
distl (x , inr z) = inr (x , z)

distr : ∀ {n} {X Y Z : Set n} → (X + Y) × Z → (X × Z) + (Y × Z)
distr (inl x , z) = inl (x , z)
distr (inr y , z) = inr (y , z)

undistl : ∀ {n} {X Y Z : Set n} → (X × Y) + (X × Z) → X × (Y + Z)
undistl (inl (x , y)) = (x , inl y)
undistl (inr (x , z)) = (x , inr z)

undistr : ∀ {n} {X Y Z : Set n} → (X × Z) + (Y × Z) → (X + Y) × Z
undistr (inl (x , z)) = (inl x , z)
undistr (inr (y , z)) = (inr y , z)