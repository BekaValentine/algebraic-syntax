{-# OPTIONS --universe-polymorphism #-}
{-# OPTIONS --no-positivity-check #-}

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Level
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import TreeIndex

module TreeCCommand where

data CCommand : {t : Tree} → (x y : TreeIndex t) → Set where
  cc-ze-lr : {l r : Tree} → CCommand {branch l r} (left root) (right root)
  cc-ze-rl : {l r : Tree} → CCommand {branch l r} (right root) (left root)
  cc-su : {t : Tree} {x y z : TreeIndex t} → CCommand x y → y < z → CCommand x z

rep-cc : (t : Tree) → (x y : TreeIndex t) → Set
rep-cc t x y = ¬ (x ≡ y) ×
               ¬ (x <⁺ y) ×
               ¬ (y <⁺ x) ×
               (Σ[ z ∶ TreeIndex t ] z < x × z <⁺ y)

{-
cc-lem : derivational-rel rep-cc
cc-lem = z , f , p
  where z : Rel₀ (TreeIndex leaf)
        z root root = ⊥
        
        f : (l r : Tree)
          → Rel₀ (TreeIndex l)
          → Rel₀ (TreeIndex r)
          → Rel₀ (TreeIndex (branch l r))
        f l r _ccl_ _ccr_ root root = ⊥
        f l r _ccl_ _ccr_ root (left y) = ⊥
        f l r _ccl_ _ccr_ root (right y) = ⊥
        f l r _ccl_ _ccr_ (left x) root = ⊥
        f l r _ccl_ _ccr_ (left x) (left y) = y ccl x
        f l r _ccl_ _ccr_ (left x) (right y) = ⊤
        f l r _ccl_ _ccr_ (right x) root = ⊥
        f l r _ccl_ _ccr_ (right x) (left y) = ⊤
        f l r _ccl_ _ccr_ (right x) (right y) = y ccr x
        
        p : (t : Tree)
          → (x y : TreeIndex t)
          → rep-cc t x y ↔ treeind (Rel₀ ∘ TreeIndex) z f t x y
        p leaf root root = fwd , bwd
          where fwd : rep-cc leaf root root → treeind (Rel₀ ∘ TreeIndex) z f leaf root root
                fwd (a , _) = ⊥-elim (a refl)
                
                bwd : treeind (Rel₀ ∘ TreeIndex) z f leaf root root → rep-cc leaf root root
                bwd ()
        
        p (branch l r) root root = fwd , bwd
          where fwd : rep-cc (branch l r) root root → treeind (Rel₀ ∘ TreeIndex) z f (branch l r) root root
                fwd (a , _) = ⊥-elim (a refl)
                
                bwd : treeind (Rel₀ ∘ TreeIndex) z f (branch l r) root root → rep-cc (branch l r) root root
                bwd ()
          
        p (branch l r) root (left y) = fwd , bwd
          where fwd : rep-cc (branch l r) root (left y) → treeind (Rel₀ ∘ TreeIndex) z f (branch l r) root (left y)
                fwd (a , b , c , d , () , f)
                
                bwd : treeind (Rel₀ ∘ TreeIndex) z f (branch l r) root (left y) → rep-cc (branch l r) root (left y)
                bwd ()
        
        p (branch l r) root (right y) = fwd , bwd
          where fwd : rep-cc (branch l r) root (right y) → treeind (Rel₀ ∘ TreeIndex) z f (branch l r) root (right y)
                fwd (a , b , c , d , () , f)
                
                bwd : treeind (Rel₀ ∘ TreeIndex) z f (branch l r) root (right y) → rep-cc (branch l r) root (right y)
                bwd ()
                
        p (branch l r) (left x) root = fwd , bwd
          where fwd : rep-cc (branch l r) (left x) root → treeind (Rel₀ ∘ TreeIndex) z f (branch l r) (left x) root
                fwd (a , b , c , d , e , <⁺-ze ())
                fwd (a , b , c , d , e , <⁺-su y ())
                
                bwd : treeind (Rel₀ ∘ TreeIndex) z f (branch l r) (left x) root → rep-cc (branch l r) (left x) root
                bwd ()
                
        p (branch l r) (left x) (left y) = fwd , bwd
          where fwd : rep-cc (branch l r) (left x) (left y) → treeind (Rel₀ ∘ TreeIndex) z f (branch l r) (left x) (left y)

                fwd (a , b , c , root , e , f) with l | x | y
                fwd (a , b , c , root , e , f) | leaf | root | root = ⊥-elim (a refl)
                fwd (a , b , c , root , <-ze-l , <⁺-ze <-ze-l) | branch l' r' | .root | .root = ⊥-elim (a refl)
                fwd (a , b , c , root , <-ze-l , <⁺-su f <-ze-l) | branch l' r' | .root | .root = ⊥-elim (a refl)
                fwd (a , b , c , root , <-ze-l , <⁺-su f (<-su-l <-ze-l)) | branch l' r' | .root | .(left root)
                  = ⊥-elim (b (cong-<⁺-left (<⁺-ze <-ze-l)))
                fwd (a , b , c , root , <-ze-l , <⁺-su f (<-su-l <-ze-r)) | branch l' r' | .root | .(right root)
                  = ⊥-elim (b (cong-<⁺-left (<⁺-ze <-ze-r)))
                fwd (a , b , c , root , <-ze-l , <⁺-su f (<-su-l (<-su-l {.l'} {.r'} {i} {j} y'))) | branch l' r' | .root | .(left j) = ⊥-elim (b (cong-<⁺-left (<⁺₀-to-<⁺ rt<⁺₀l)))
                fwd (a , b , c , root , <-ze-l , <⁺-su f (<-su-l (<-su-r {.l'} {.r'} {i} {j} y'))) | branch l' r' | .root | .(right j) = ⊥-elim (b (cong-<⁺-left (<⁺₀-to-<⁺ rt<⁺₀r)))
                fwd (a , b , c , left d , e , f) with l | x | y
                fwd (a , b , c , left d , e , f) | leaf | root | root = ⊥-elim (a refl)
                fwd (a , b , c , left d , e , f) | branch l' r' | root | root = ⊥-elim (a refl)
                fwd (a , b , c , left d , e , f) | branch l' r' | left x' | root = ⊥-elim (c (cong-<⁺-left rt<⁺l))
                fwd (a , b , c , left d , e , f) | branch l' r' | right x' | root = ⊥-elim (c (cong-<⁺-left rt<⁺r))
                fwd (a , b , c , left d , e , f) | branch l' r' | root | left y' = ⊥-elim (b (cong-<⁺-left rt<⁺l))
                fwd (a , b , c , left d , e , <⁺-ze y0) | branch l' r' | left x' | left y'
                  = proj₁ (p (branch l' r') (left y') (left x'))
                    ((λ ly'=lx' → a (sym (cong left ly'=lx'))) ,
                        (λ ly'<+lx' → c (cong-<⁺-left ly'<+lx')) ,
                        (λ lx'<+ly' → b (cong-<⁺-left lx'<+ly')) ,
                      d , uncong-<-left y0 , uncong-<⁺-left (<⁺-ze e))
                fwd (a , b , c , left d , e , <⁺-su y0 (<-su-l <-ze-l)) | branch l' r' | left x' | left .root = ⊥-elim (¬i<⁺rt (uncong-<⁺-left y0))
                fwd (a , b , c , left .root , <-su-l <-ze-l , <⁺-su y0 (<-su-l (<-su-l y1))) | branch l' r' | left .root | left y' = ⊥-elim (b (cong-<⁺-left (cong-<⁺-left (<⁺-su {!!} y1))))
                fwd (a , b , c , left .(left i) , <-su-l (<-su-l {.l'} {.r'} {i} y0) , <⁺-su y1 (<-su-l (<-su-l y2))) | branch l' r' | left x' | left y' = {!!}
                fwd (a , b , c , left d , e , f) | branch l' r' | right x' | left y' = tt
                fwd (a , b , c , left d , e , f) | branch l' r' | x' | right y' = {!!} 
                fwd (a , b , c , right d , e , f) with l | x | y
                fwd (a , b , c , right d , e , f) | leaf | root | root = ⊥-elim (a refl)
                fwd (a , b , c , right d , e , f) | branch l' r' | x' | y' = {!!}

{-
                fwd (a , b , c , d , e , f) with l | x | y
                fwd (a , b , c , d , e , f) | leaf | root | root = ⊥-elim (a refl)
                fwd (a , b , c , d , e , f) | branch leaf leaf | root | root = ⊥-elim (a refl)
                fwd (a , b , c , d , e , f) | branch leaf leaf | root | left root = ⊥-elim (b (cong-<⁺-left (<⁺-ze <-ze-l)))
                fwd (a , b , c , d , e , f) | branch leaf leaf | root | right root = ⊥-elim (b (cong-<⁺-left (<⁺-ze <-ze-r)))
                fwd (a , b , c , d , e , f) | branch leaf leaf | left root | root = ⊥-elim (c (cong-<⁺-left (<⁺-ze <-ze-l)))
                fwd (a , b , c , d , e , f) | branch leaf leaf | left root | left root = ⊥-elim (a refl)
                fwd (a , b , c , d , e , f) | branch leaf leaf | left root | right root
                  = proj₁ (p (branch leaf leaf) (left root) (right root))
                         ((λ ()) ,
                           ff , gg , root , <-ze-l , (<⁺-ze <-ze-r))
                  where ff : ¬ left {leaf} {leaf} root <⁺ right {leaf} {leaf} root
                        ff (<⁺-ze ())
                        ff (<⁺-su (<⁺-ze ()) <-ze-r)
                        ff (<⁺-su (<⁺-su y' ()) <-ze-r)
                        ff (<⁺-su y' (<-su-r ()))
                        
                        gg : ¬ right {leaf} {leaf} root <⁺ left {leaf} {leaf} root
                        gg (<⁺-ze ())
                        gg (<⁺-su (<⁺-ze ()) <-ze-l)
                        gg (<⁺-su (<⁺-su y' ()) <-ze-l)
                        gg (<⁺-su y' (<-su-l ()))
                
                fwd (a , b , c , d , e , f) | branch leaf leaf | right root | root = ⊥-elim (c (cong-<⁺-left (<⁺-ze <-ze-r)))
                fwd (a , b , c , d , e , f) | branch leaf leaf | right root | left root
                  = proj₁ (p (branch leaf leaf) (right root) (left root))
                          ((λ ()) ,
                            gg , ff , root , <-ze-r , <⁺-ze <-ze-l)
                  where ff : ¬ left {leaf} {leaf} root <⁺ right {leaf} {leaf} root
                        ff (<⁺-ze ())
                        ff (<⁺-su (<⁺-ze ()) <-ze-r)
                        ff (<⁺-su (<⁺-su y' ()) <-ze-r)
                        ff (<⁺-su y' (<-su-r ()))
                        
                        gg : ¬ right {leaf} {leaf} root <⁺ left {leaf} {leaf} root
                        gg (<⁺-ze ())
                        gg (<⁺-su (<⁺-ze ()) <-ze-l)
                        gg (<⁺-su (<⁺-su y' ()) <-ze-l)
                        gg (<⁺-su y' (<-su-l ()))
                
                fwd (a , b , c , d , e , f) | branch l' r' | root | root = ⊥-elim (a refl)
                fwd (a , b , c , d , e , f) | branch l' r' | root | left root = ⊥-elim (b (cong-<⁺-left (<⁺-ze <-ze-l)))
                fwd (a , b , c , d , e , f) | branch l' r' | root | left y' = ⊥-elim (b (<⁺₀-to-<⁺ (cong-<⁺₀-left rt<⁺₀l)))
                fwd (a , b , c , d , e , f) | branch l' r' | root | right y' = ⊥-elim (b (<⁺₀-to-<⁺ (cong-<⁺₀-left rt<⁺₀r)))
                fwd (a , b , c , d , e , f) | branch l' r' | left x' | root = ⊥-elim (c (<⁺₀-to-<⁺ (cong-<⁺₀-left rt<⁺₀l)))
                fwd (a , b , c , root , () , f) | branch l' r' | left x' | left y'
                fwd (a , b , c , left root , e , f) | branch l' r' | left x' | left y' = {!!}
                fwd (a , b , c , left (left y0) , e , f) | branch l' r' | left x' | left y' = {!!}
                fwd (a , b , c , left (right y0) , e , f) | branch l' r' | left x' | left y' = {!!}
                fwd (a , b , c , right d , () , f) | branch l' r' | left x' | left y'
                fwd (a , b , c , d , e , f) | branch l' r' | left x' | right y' = {!!}
                fwd (a , b , c , d , e , f) | branch l' r' | right x' | root = ⊥-elim (c (<⁺₀-to-<⁺ (cong-<⁺₀-left rt<⁺₀r)))
                fwd (a , b , c , d , e , f) | branch l' r' | right x' | left y' = {!!}
                fwd (a , b , c , d , e , f) | branch l' r' | right x' | right y' = {!!}
-}
                bwd : treeind (Rel₀ ∘ TreeIndex) z f (branch l r) (left x) (left y) → rep-cc (branch l r) (left x) (left y)
                bwd rr = {!!}
                
        p (branch l r) (left x) (right y) = {!!}
        p (branch l r) (right x) root = {!!}
        p (branch l r) (right x) (left y) = {!!}
        p (branch l r) (right x) (right y) = {!!}

--rep-cc _ → treeind (Rel₀ ∘ TreeIndex) z f _
-}