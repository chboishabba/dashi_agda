module DASHI.Foundations.C3NineSiteAlternatingOrbitExact where

-- Finite, proof-carrying spine for the user's alternating 12-step orbit.
-- This is *not* yet a proof of a continuous braid isotopy or a Hopf fibration.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)

data Site : Set where
  TL TM TR ML MM MR BL BM BR : Site

data T12 : Set where
  t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : T12

next : T12 → T12
next t0 = t1
next t1 = t2
next t2 = t3
next t3 = t4
next t4 = t5
next t5 = t6
next t6 = t7
next t7 = t8
next t8 = t9
next t9 = t10
next t10 = t11
next t11 = t0

shift4 : T12 → T12
shift4 t0 = t4
shift4 t1 = t5
shift4 t2 = t6
shift4 t3 = t7
shift4 t4 = t8
shift4 t5 = t9
shift4 t6 = t10
shift4 t7 = t11
shift4 t8 = t0
shift4 t9 = t1
shift4 t10 = t2
shift4 t11 = t3

phase3 : ∀ t → shift4 (shift4 (shift4 t)) ≡ t
phase3 t0 = refl
phase3 t1 = refl
phase3 t2 = refl
phase3 t3 = refl
phase3 t4 = refl
phase3 t5 = refl
phase3 t6 = refl
phase3 t7 = refl
phase3 t8 = refl
phase3 t9 = refl
phase3 t10 = refl
phase3 t11 = refl

orbit : T12 → Site
orbit t0 = TL
orbit t1 = TM
orbit t2 = MM
orbit t3 = BM
orbit t4 = BR
orbit t5 = MR
orbit t6 = TR
orbit t7 = TM
orbit t8 = MM
orbit t9 = BM
orbit t10 = BL
orbit t11 = ML

record Triple (A : Set) : Set where
  constructor triple
  field first second third : A
open Triple public

configuration : T12 → Triple Site
configuration t = triple (orbit t) (orbit (shift4 t))
                         (orbit (shift4 (shift4 t)))

rotate : Triple Site → Triple Site
rotate (triple a b c) = triple b c a

rotateConfiguration : ∀ t →
  configuration (shift4 t) ≡ rotate (configuration t)
rotateConfiguration t0 = refl
rotateConfiguration t1 = refl
rotateConfiguration t2 = refl
rotateConfiguration t3 = refl
rotateConfiguration t4 = refl
rotateConfiguration t5 = refl
rotateConfiguration t6 = refl
rotateConfiguration t7 = refl
rotateConfiguration t8 = refl
rotateConfiguration t9 = refl
rotateConfiguration t10 = refl
rotateConfiguration t11 = refl

siteEq : Site → Site → Bool
siteEq TL TL = true
siteEq TM TM = true
siteEq TR TR = true
siteEq ML ML = true
siteEq MM MM = true
siteEq MR MR = true
siteEq BL BL = true
siteEq BM BM = true
siteEq BR BR = true
siteEq _ _ = false

distinct : Triple Site → Bool
distinct (triple a b c) with siteEq a b | siteEq b c | siteEq a c
... | false | false | false = true
... | _ | _ | _ = false

configurationDistinct : ∀ t → distinct (configuration t) ≡ true
configurationDistinct t0 = refl
configurationDistinct t1 = refl
configurationDistinct t2 = refl
configurationDistinct t3 = refl
configurationDistinct t4 = refl
configurationDistinct t5 = refl
configurationDistinct t6 = refl
configurationDistinct t7 = refl
configurationDistinct t8 = refl
configurationDistinct t9 = refl
configurationDistinct t10 = refl
configurationDistinct t11 = refl

-- Critical boundary: vertex distinctness does not imply collision-free
-- interpolation, and finite cyclic equivariance does not imply a braid word.
