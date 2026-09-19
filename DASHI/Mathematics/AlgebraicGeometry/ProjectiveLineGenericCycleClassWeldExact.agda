module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineGenericCycleClassWeldExact where

------------------------------------------------------------------------
-- PROJECTIVE-LINE FINITE MODEL -> GENERIC HODGE CYCLE-CLASS WELD
--
-- The repository already proves literal surjectivity of the Q-valued P^1
-- cycle-class model.  This module isolates the exact same-object bridge needed
-- to transport that finite theorem onto a supplied generic Hodge cycle map.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineCycleClassExact as P1

record ProjectiveLineGenericCycleClassWeld
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (cycleMap : Hodge.CycleClassMap variety comparison hodge) : Set₁ where
  field
    cycleFromP1 :
      P1.P1RationalDivisorCycle →
      Hodge.Cycle cycleMap 1

    h11FromGeneric :
      Hodge.RationalHodgeClass hodge 1 →
      P1.P1RationalH11Class

    genericFromP1 :
      P1.P1RationalH11Class →
      Hodge.RationalHodgeClass hodge 1

    h11RoundTrip :
      (h : Hodge.RationalHodgeClass hodge 1) →
      genericFromP1 (h11FromGeneric h) ≡ h

    cycleClassCommutes :
      (z : P1.P1RationalDivisorCycle) →
      Hodge.cycleClass cycleMap 1 (cycleFromP1 z)
      ≡ Hodge.hodgeClassValue
          (genericFromP1 (P1.p1CycleClass z))

open ProjectiveLineGenericCycleClassWeld public

genericP1CycleRepresentative :
  ∀ {variety comparison hodge cycleMap} →
  ProjectiveLineGenericCycleClassWeld
    {variety = variety}
    {comparison = comparison}
    {hodge = hodge}
    cycleMap →
  Hodge.RationalHodgeClass hodge 1 →
  Hodge.Cycle cycleMap 1
genericP1CycleRepresentative weld h =
  cycleFromP1 weld
    (P1.cycleRepresentingH11Class (h11FromGeneric weld h))

genericP1CycleRepresents :
  ∀ {variety comparison hodge cycleMap}
    (weld :
      ProjectiveLineGenericCycleClassWeld
        {variety = variety}
        {comparison = comparison}
        {hodge = hodge}
        cycleMap)
    (h : Hodge.RationalHodgeClass hodge 1) →
  Hodge.cycleClass cycleMap 1
    (genericP1CycleRepresentative weld h)
  ≡ Hodge.hodgeClassValue h
genericP1CycleRepresents weld h
    rewrite P1.p1CycleClassSurjective (h11FromGeneric weld h)
          | h11RoundTrip weld h =
  cycleClassCommutes weld
    (P1.cycleRepresentingH11Class (h11FromGeneric weld h))

genericP1WeldGivesHodgeAtOne :
  ∀ {variety comparison hodge cycleMap} →
  ProjectiveLineGenericCycleClassWeld
    {variety = variety}
    {comparison = comparison}
    {hodge = hodge}
    cycleMap →
  Hodge.HodgeConjectureAtCodimension cycleMap 1
genericP1WeldGivesHodgeAtOne weld = record
  { Hodge.everyRationalHodgeClassHasCycle =
      genericP1CycleRepresentative weld
  ; Hodge.cycleRepresentsClass =
      genericP1CycleRepresents weld
  }

record ProjectiveLineGenericCycleWeldBoundary : Set where
  constructor projective-line-generic-cycle-weld-boundary
  field
    projectiveLineFiniteSurjectivityPaid : Bool
    projectiveLineGenericCycleWeldCompilerPaid : Bool
    literalP1GeometryWeldPaid : Bool
    literalCPnComparisonPaid : Bool
    generalHodgeConjecturePaid : Bool

canonicalProjectiveLineGenericCycleWeldBoundary :
  ProjectiveLineGenericCycleWeldBoundary
canonicalProjectiveLineGenericCycleWeldBoundary =
  projective-line-generic-cycle-weld-boundary
    true true false false false
