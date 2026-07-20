module DASHI.Foundations.Base369TriadicPhaseTower where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import Base369 using
  ( TriTruth
  ; NonaryTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  ; non-0
  ; non-1
  ; non-2
  ; non-3
  ; non-4
  ; non-5
  ; non-6
  ; non-7
  ; non-8
  )
open import DASHI.Foundations.Base369CirclePhase using
  (triToNonary)

------------------------------------------------------------------------
-- A concrete first fragment of C3 -> C9 -> C27.

nonaryToTriSector : NonaryTruth → TriTruth
nonaryToTriSector non-0 = tri-low
nonaryToTriSector non-1 = tri-low
nonaryToTriSector non-2 = tri-low
nonaryToTriSector non-3 = tri-mid
nonaryToTriSector non-4 = tri-mid
nonaryToTriSector non-5 = tri-mid
nonaryToTriSector non-6 = tri-high
nonaryToTriSector non-7 = tri-high
nonaryToTriSector non-8 = tri-high

triToNonary-section :
  (t : TriTruth) →
  nonaryToTriSector (triToNonary t) ≡ t
triToNonary-section tri-low = refl
triToNonary-section tri-mid = refl
triToNonary-section tri-high = refl

data Phase27 : Set where
  p27-0 p27-1 p27-2 p27-3 p27-4 p27-5 p27-6 p27-7 p27-8 : Phase27
  p27-9 p27-10 p27-11 p27-12 p27-13 p27-14 p27-15 p27-16 p27-17 : Phase27
  p27-18 p27-19 p27-20 p27-21 p27-22 p27-23 p27-24 p27-25 p27-26 : Phase27

nonaryTo27 : NonaryTruth → Phase27
nonaryTo27 non-0 = p27-0
nonaryTo27 non-1 = p27-3
nonaryTo27 non-2 = p27-6
nonaryTo27 non-3 = p27-9
nonaryTo27 non-4 = p27-12
nonaryTo27 non-5 = p27-15
nonaryTo27 non-6 = p27-18
nonaryTo27 non-7 = p27-21
nonaryTo27 non-8 = p27-24

phase27ToNonarySector : Phase27 → NonaryTruth
phase27ToNonarySector p27-0 = non-0
phase27ToNonarySector p27-1 = non-0
phase27ToNonarySector p27-2 = non-0
phase27ToNonarySector p27-3 = non-1
phase27ToNonarySector p27-4 = non-1
phase27ToNonarySector p27-5 = non-1
phase27ToNonarySector p27-6 = non-2
phase27ToNonarySector p27-7 = non-2
phase27ToNonarySector p27-8 = non-2
phase27ToNonarySector p27-9 = non-3
phase27ToNonarySector p27-10 = non-3
phase27ToNonarySector p27-11 = non-3
phase27ToNonarySector p27-12 = non-4
phase27ToNonarySector p27-13 = non-4
phase27ToNonarySector p27-14 = non-4
phase27ToNonarySector p27-15 = non-5
phase27ToNonarySector p27-16 = non-5
phase27ToNonarySector p27-17 = non-5
phase27ToNonarySector p27-18 = non-6
phase27ToNonarySector p27-19 = non-6
phase27ToNonarySector p27-20 = non-6
phase27ToNonarySector p27-21 = non-7
phase27ToNonarySector p27-22 = non-7
phase27ToNonarySector p27-23 = non-7
phase27ToNonarySector p27-24 = non-8
phase27ToNonarySector p27-25 = non-8
phase27ToNonarySector p27-26 = non-8

nonaryTo27-section :
  (n : NonaryTruth) →
  phase27ToNonarySector (nonaryTo27 n) ≡ n
nonaryTo27-section non-0 = refl
nonaryTo27-section non-1 = refl
nonaryTo27-section non-2 = refl
nonaryTo27-section non-3 = refl
nonaryTo27-section non-4 = refl
nonaryTo27-section non-5 = refl
nonaryTo27-section non-6 = refl
nonaryTo27-section non-7 = refl
nonaryTo27-section non-8 = refl

triTo27 : TriTruth → Phase27
triTo27 t = nonaryTo27 (triToNonary t)

phase27ToTriSector : Phase27 → TriTruth
phase27ToTriSector x =
  nonaryToTriSector (phase27ToNonarySector x)

triTo27-section :
  (t : TriTruth) →
  phase27ToTriSector (triTo27 t) ≡ t
triTo27-section tri-low = refl
triTo27-section tri-mid = refl
triTo27-section tri-high = refl

------------------------------------------------------------------------
-- Generic finite tower-step contract.

record TriadicTowerStep (Coarse Fine : Set) : Set where
  constructor triadicTowerStep
  field
    lift : Coarse → Fine
    project : Fine → Coarse
    projectAfterLift :
      (x : Coarse) →
      project (lift x) ≡ x

open TriadicTowerStep public

c3ToC9Step : TriadicTowerStep TriTruth NonaryTruth
c3ToC9Step =
  triadicTowerStep
    triToNonary
    nonaryToTriSector
    triToNonary-section

c9ToC27Step : TriadicTowerStep NonaryTruth Phase27
c9ToC27Step =
  triadicTowerStep
    nonaryTo27
    phase27ToNonarySector
    nonaryTo27-section

record TriadicPhaseTowerFragmentReceipt : Set where
  constructor triadicPhaseTowerFragmentReceipt
  field
    level3 : Set
    level9 : Set
    level27 : Set
    firstStep : TriadicTowerStep level3 level9
    secondStep : TriadicTowerStep level9 level27
    twoStepSection :
      (x : level3) →
      project firstStep
        (project secondStep
          (lift secondStep (lift firstStep x)))
      ≡ x
    finiteTowerChecked : Bool
    infiniteInverseLimitPromoted : Bool
    infiniteInverseLimitPromotedIsFalse :
      infiniteInverseLimitPromoted ≡ false
    boundary : String

base369TriadicPhaseTowerFragmentReceipt :
  TriadicPhaseTowerFragmentReceipt
base369TriadicPhaseTowerFragmentReceipt =
  triadicPhaseTowerFragmentReceipt
    TriTruth
    NonaryTruth
    Phase27
    c3ToC9Step
    c9ToC27Step
    triTo27-section
    true
    false
    refl
    "The finite C3-C9-C27 lift/project fragment is checked. A generic C_(3^n) inverse system, 3-adic completion, and analytic phase interpretation remain separate theorem layers."
