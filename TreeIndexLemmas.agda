{-# OPTIONS --universe-polymorphism #-}

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Level
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module TreeIndexLemmas where



¬l≡r : {l r : Tree} → {x : TreeIndex l} → {y : TreeIndex r} → ¬ left x ≡ right y
¬l≡r ()

¬r≡l : {l r : Tree} → {x : TreeIndex r} → {y : TreeIndex l} → ¬ right x ≡ left y
¬r≡l ()

uncong-<-left : {l r : Tree} → {x y : TreeIndex l} → left {l} {r} x < left {l} {r} y → x < y
uncong-<-left (<-su-l y') = y'

uncong-<-right : {l r : Tree} → {x y : TreeIndex r} → right {l} {r} x < right {l} {r} y → x < y
uncong-<-right (<-su-r y') = y'


¬i<rt : {t : Tree} {i : TreeIndex t}
      → ¬ i < root
¬i<rt ()

¬i<⁺rt : {t : Tree} → {i : TreeIndex t} → ¬ i <⁺ root
¬i<⁺rt (<⁺-ze ())
¬i<⁺rt (<⁺-su y ())

cong-<⁺-left : {l r : Tree} → {x y : TreeIndex l} → x <⁺ y → left {l} {r} x <⁺ left {l} {r} y
cong-<⁺-left (<⁺-ze r) = <⁺-ze (<-su-l r)
cong-<⁺-left (<⁺-su r s) = <⁺-su (cong-<⁺-left r) (<-su-l s)

cong-<⁺-right : {l r : Tree} → {x y : TreeIndex r} → x <⁺ y → right {l} {r} x <⁺ right {l} {r} y
cong-<⁺-right (<⁺-ze z) = <⁺-ze (<-su-r z)
cong-<⁺-right (<⁺-su r s) = <⁺-su (cong-<⁺-right r) (<-su-r s)

cong-<⁺₀-left : {l r : Tree} → {x y : TreeIndex l} → x <⁺₀ y → left {l} {r} x <⁺₀ left {l} {r} y
cong-<⁺₀-left (<⁺₀-ze r) = <⁺₀-ze (<-su-l r)
cong-<⁺₀-left (<⁺₀-su r s) = <⁺₀-su (<-su-l r) (cong-<⁺₀-left s)

cong-<⁺₀-right : {l r : Tree} → {x y : TreeIndex r} → x <⁺₀ y → right {l} {r} x <⁺₀ right {l} {r} y
cong-<⁺₀-right (<⁺₀-ze z) = <⁺₀-ze (<-su-r z)
cong-<⁺₀-right (<⁺₀-su r s) = <⁺₀-su (<-su-r r) (cong-<⁺₀-right s)

mutual
  rt<⁺₀l : {l r : Tree} → {x : TreeIndex l} → root <⁺₀ left {l} {r} x
  rt<⁺₀l {leaf} {r} {root} = <⁺₀-ze <-ze-l
  rt<⁺₀l {branch y y'} {r} {root} = <⁺₀-ze <-ze-l
  rt<⁺₀l {branch y y'} {r} {left y0} = <⁺₀-su <-ze-l (cong-<⁺₀-left rt<⁺₀l)
  rt<⁺₀l {branch y y'} {r} {right y0} = <⁺₀-su <-ze-l (cong-<⁺₀-left rt<⁺₀r)
  
  rt<⁺₀r : {l r : Tree} → {x : TreeIndex r} → root <⁺₀ right {l} {r} x
  rt<⁺₀r {l} {leaf} {root} = <⁺₀-ze <-ze-r
  rt<⁺₀r {l} {branch y y'} {root} = <⁺₀-ze <-ze-r
  rt<⁺₀r {l} {branch y y'} {left y0} = <⁺₀-su <-ze-r (cong-<⁺₀-right rt<⁺₀l)
  rt<⁺₀r {l} {branch y y'} {right y0} = <⁺₀-su <-ze-r (cong-<⁺₀-right rt<⁺₀r)

<⁺-to-<⁺₀ : {t : Tree} {x y : TreeIndex t} → x <⁺ y → x <⁺₀ y
<⁺-to-<⁺₀ (<⁺-ze y) = <⁺₀-ze y
<⁺-to-<⁺₀ (<⁺-su y y') = go y (<⁺₀-ze y')
  where go : {t : Tree} → {x y z : TreeIndex t} → x <⁺ y → y <⁺₀ z → x <⁺₀ z
        go (<⁺-ze y1) ss = <⁺₀-su y1 ss
        go (<⁺-su y1 y2) ss = go y1 (<⁺₀-su y2 ss)

<⁺₀-to-<⁺ : {t : Tree} {x y : TreeIndex t} → x <⁺₀ y → x <⁺ y
<⁺₀-to-<⁺ (<⁺₀-ze y) = <⁺-ze y
<⁺₀-to-<⁺ (<⁺₀-su y y') = go (<⁺-ze y) y'
  where go : {t : Tree} → {x y z : TreeIndex t} → x <⁺ y → y <⁺₀ z → x <⁺ z
        go rr (<⁺₀-ze y1) = <⁺-su rr y1
        go rr (<⁺₀-su y1 y2) = go (<⁺-su rr y1) y2

rt<⁺l : {l r : Tree} → {x : TreeIndex l} → root <⁺ left {l} {r} x
rt<⁺l = <⁺₀-to-<⁺ rt<⁺₀l

rt<⁺r : {l r : Tree} → {x : TreeIndex r} → root <⁺ right {l} {r} x
rt<⁺r = <⁺₀-to-<⁺ rt<⁺₀r

uncong-<⁺-left : {l r : Tree} → {x y : TreeIndex l} → left {l} {r} x <⁺ left {l} {r} y → x <⁺ y
uncong-<⁺-left (<⁺-ze (<-su-l y')) = <⁺-ze y'
uncong-<⁺-left (<⁺-su (<⁺-ze ()) <-ze-l)
uncong-<⁺-left (<⁺-su (<⁺-su y ()) <-ze-l)
uncong-<⁺-left (<⁺-su y' (<-su-l y0)) = <⁺-su (uncong-<⁺-left y') y0

uncong-<⁺-right : {l r : Tree} → {x y : TreeIndex r} → right {l} {r} x <⁺ right {l} {r} y → x <⁺ y
uncong-<⁺-right (<⁺-ze (<-su-r y')) = <⁺-ze y'
uncong-<⁺-right (<⁺-su (<⁺-ze ()) <-ze-r)
uncong-<⁺-right (<⁺-su (<⁺-su y ()) <-ze-r)
uncong-<⁺-right (<⁺-su y' (<-su-r y0)) = <⁺-su (uncong-<⁺-right y') y0

intrans-< : {t : Tree} → {x y z : TreeIndex t} → x < y → y < z → ¬ x < z
intrans-< <-ze-l (<-su-l ()) <-ze-l
intrans-< <-ze-r (<-su-r ()) <-ze-r
intrans-< (<-su-l x) (<-su-l y) (<-su-l z) = intrans-< x y z
intrans-< (<-su-r x) (<-su-r y) (<-su-r z) = intrans-< x y z

single-root : {t : Tree} → {x y z : TreeIndex t} → x < z → y < z → x ≡ y
single-root <-ze-l <-ze-l = refl
single-root <-ze-l (<-su-l ())
single-root <-ze-r <-ze-r = refl
single-root <-ze-r (<-su-r ())
single-root (<-su-l ()) <-ze-l
single-root (<-su-l x) (<-su-l y) = cong left (single-root x y)
single-root (<-su-r ()) <-ze-r
single-root (<-su-r x) (<-su-r y) = cong right (single-root x y)

irrefl-< : {t : Tree} → {x : TreeIndex t} → x < x → ⊥
irrefl-< {leaf} {root} ()
irrefl-< {branch l r} {root} ()
irrefl-< {branch l r} {left x} (<-su-l x<x) = irrefl-< x<x
irrefl-< {branch l r} {right x} (<-su-r x<x) = irrefl-< x<x

asym-< : {t : Tree} → {x y : TreeIndex t} → x < y → y < x → ⊥
asym-< <-ze-l ()
asym-< <-ze-r ()
asym-< (<-su-l x) (<-su-l y) = asym-< x y
asym-< (<-su-r x) (<-su-r y) = asym-< x y

trans-<⁺ : {t : Tree} → {x y z : TreeIndex t} → x <⁺ y → y <⁺ z → x <⁺ z
trans-<⁺ x<+y (<⁺-ze y') = <⁺-su x<+y y'
trans-<⁺ x<+y (<⁺-su y' y0) = <⁺-su (trans-<⁺ x<+y y') y0

irrefl-<⁺ : {t : Tree} → {x : TreeIndex t} → x <⁺ x → ⊥
irrefl-<⁺ (<⁺-ze x<x) = irrefl-< x<x
irrefl-<⁺ (<⁺-su (<⁺-ze y) y') = asym-< y y'
irrefl-<⁺ (<⁺-su (<⁺-su y ()) <-ze-l)
irrefl-<⁺ (<⁺-su (<⁺-su y ()) <-ze-r)
irrefl-<⁺ (<⁺-su (<⁺-su y <-ze-l) (<-su-l y'')) = ¬i<⁺rt y
irrefl-<⁺ (<⁺-su (<⁺-su y' (<-su-l <-ze-l)) (<-su-l y'')) = ¬i<⁺rt (uncong-<⁺-left y')
irrefl-<⁺ (<⁺-su (<⁺-su y' (<-su-l <-ze-r)) (<-su-l y'')) = ¬i<⁺rt (uncong-<⁺-left y')
irrefl-<⁺ (<⁺-su (<⁺-su y' (<-su-l (<-su-l y))) (<-su-l (<-su-l y0))) = irrefl-<⁺ (trans-<⁺ (uncong-<⁺-left (uncong-<⁺-left y')) (<⁺-su (<⁺-ze y) y0))
irrefl-<⁺ (<⁺-su (<⁺-su y' (<-su-l (<-su-r y))) (<-su-l (<-su-r y0))) = irrefl-<⁺ (trans-<⁺ (uncong-<⁺-right (uncong-<⁺-left y')) (<⁺-su (<⁺-ze y) y0))
irrefl-<⁺ (<⁺-su (<⁺-su y <-ze-r) (<-su-r y'')) = ¬i<⁺rt y
irrefl-<⁺ (<⁺-su (<⁺-su y' (<-su-r <-ze-l)) (<-su-r y'')) = ¬i<⁺rt (uncong-<⁺-right y')
irrefl-<⁺ (<⁺-su (<⁺-su y' (<-su-r <-ze-r)) (<-su-r y'')) = ¬i<⁺rt (uncong-<⁺-right y')
irrefl-<⁺ (<⁺-su (<⁺-su y' (<-su-r (<-su-l y))) (<-su-r (<-su-l y0))) = irrefl-<⁺ (trans-<⁺ (uncong-<⁺-left (uncong-<⁺-right y')) (<⁺-su (<⁺-ze y) y0))
irrefl-<⁺ (<⁺-su (<⁺-su y' (<-su-r (<-su-r y))) (<-su-r (<-su-r y0))) = irrefl-<⁺ (trans-<⁺ (uncong-<⁺-right (uncong-<⁺-right y')) (<⁺-su (<⁺-ze y) y0))

<⁺-<-sep : {t : Tree} → {x y z : TreeIndex t} → y < z → x < z → x <⁺ y → ⊥
<⁺-<-sep yz xz xy with single-root yz xz
<⁺-<-sep yz xz xy | refl = irrefl-<⁺ xy