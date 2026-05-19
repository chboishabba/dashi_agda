module Ontology.Hecke.DefectOrbitCollapsePressure where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

open import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
  using
    ( CollapseTime
    ; GeneratorCollapseClass
    ; collapseTime
    ; exitToAnchored
    ; immediateExit
    ; staysOneMoreStep
    ; unknownCollapse
    )
open import Ontology.Hecke.DefectOrbitCollapseBridge as DOCB
  using
    ( illegalCountP2
    ; forcedStableCountOrbitP2
    ; illegalCount≤forcedStableCountOrbitP2
    )

------------------------------------------------------------------------
-- First pressure layer above the collapse-time observable.
--
-- This remains intentionally coarse.  The current bridge only gives a
-- representative-state lower bound at `p2`, so the pressure tier should be
-- read as a classified summary surface, not yet as a Hecke-determined
-- quotient.

data PressureClass : Set where
  lowPressure : PressureClass
  mediumPressure : PressureClass
  highPressure : PressureClass

pressureClass : GeneratorCollapseClass → PressureClass
pressureClass c with collapseTime c
... | immediateExit = highPressure
... | exitToAnchored = mediumPressure
... | staysOneMoreStep = lowPressure
... | unknownCollapse = lowPressure

pressureClass-explicit-immediateExit :
  ∀ c →
  collapseTime c ≡ immediateExit →
  pressureClass c ≡ highPressure
pressureClass-explicit-immediateExit c eq rewrite eq = refl

pressureClass-explicit-exitToAnchored :
  ∀ c →
  collapseTime c ≡ exitToAnchored →
  pressureClass c ≡ mediumPressure
pressureClass-explicit-exitToAnchored c eq rewrite eq = refl

pressureClass-explicit-staysOneMoreStep :
  ∀ c →
  collapseTime c ≡ staysOneMoreStep →
  pressureClass c ≡ lowPressure
pressureClass-explicit-staysOneMoreStep c eq rewrite eq = refl

pressureClass-unknownCollapse :
  ∀ c →
  collapseTime c ≡ unknownCollapse →
  pressureClass c ≡ lowPressure
pressureClass-unknownCollapse c eq rewrite eq = refl

------------------------------------------------------------------------
-- Current honest pressure theorem:
-- every classified representative already inherits the existing `p2`
-- lower-bound ladder from the bridge module.

pressureLowerBoundAtP2 :
  ∀ c →
  illegalCountP2 c ≤ forcedStableCountOrbitP2 c
pressureLowerBoundAtP2 = illegalCount≤forcedStableCountOrbitP2

highPressure-gives-orbitLowerBound :
  ∀ c →
  pressureClass c ≡ highPressure →
  illegalCountP2 c ≤ forcedStableCountOrbitP2 c
highPressure-gives-orbitLowerBound c _ = pressureLowerBoundAtP2 c

mediumPressure-gives-orbitLowerBound :
  ∀ c →
  pressureClass c ≡ mediumPressure →
  illegalCountP2 c ≤ forcedStableCountOrbitP2 c
mediumPressure-gives-orbitLowerBound c _ = pressureLowerBoundAtP2 c

lowPressure-gives-orbitLowerBound :
  ∀ c →
  pressureClass c ≡ lowPressure →
  illegalCountP2 c ≤ forcedStableCountOrbitP2 c
lowPressure-gives-orbitLowerBound c _ = pressureLowerBoundAtP2 c

record DefectPressureSummary : Set where
  constructor defectPressureSummary
  field
    pressureTier : PressureClass
    illegalAtP2 : Nat
    forcedStableOrbitAtP2 : Nat

defectPressureSummaryAt :
  GeneratorCollapseClass → DefectPressureSummary
defectPressureSummaryAt c =
  defectPressureSummary
    (pressureClass c)
    (illegalCountP2 c)
    (forcedStableCountOrbitP2 c)

summaryLowerBoundAtP2 :
  ∀ c →
  DefectPressureSummary.illegalAtP2 (defectPressureSummaryAt c)
    ≤
  DefectPressureSummary.forcedStableOrbitAtP2
    (defectPressureSummaryAt c)
summaryLowerBoundAtP2 c = pressureLowerBoundAtP2 c
