module DASHI.TrackedPrimes where

open import Agda.Builtin.List using (List; []; _∷_)

open import MonsterOntos public using
  ( SSP
  ; toNat
  ; toNat-injective
  ; _≟_
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

------------------------------------------------------------------------
-- Canonical tracked-prime carrier.
--
-- Many repo modules need the same finite carrier in both list and Vec15 form.
-- Centralising it keeps the 15-prime enumeration in one place and lets
-- downstream modules express lanewise structure via a single mapper.

trackedPrimeList : List SSP
trackedPrimeList =
  p2 ∷ p3 ∷ p5 ∷ p7 ∷ p11 ∷ p13 ∷ p17 ∷ p19 ∷ p23 ∷ p29 ∷ p31 ∷ p41 ∷ p47 ∷ p59 ∷ p71 ∷ []

trackedPrimeVec15 : Vec15 SSP
trackedPrimeVec15 =
  mkVec15 p2 p3 p5 p7 p11 p13 p17 p19 p23 p29 p31 p41 p47 p59 p71

mapTrackedPrimes15 : ∀ {A : Set} → (SSP → A) → Vec15 A
mapTrackedPrimes15 f =
  mkVec15
    (f p2) (f p3) (f p5) (f p7) (f p11)
    (f p13) (f p17) (f p19) (f p23) (f p29)
    (f p31) (f p41) (f p47) (f p59) (f p71)
