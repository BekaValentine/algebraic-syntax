module Naturals where



data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN LEVEL     ℕ #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

_⊔_ : ℕ → ℕ → ℕ
zero ⊔ n = n
m ⊔ zero = m
suc m ⊔ suc n = suc (m ⊔ n)

{-# BUILTIN LEVELMAX _⊔_ #-}