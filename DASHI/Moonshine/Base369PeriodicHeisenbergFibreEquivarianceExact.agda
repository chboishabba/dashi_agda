module DASHI.Moonshine.Base369PeriodicHeisenbergFibreEquivarianceExact where

------------------------------------------------------------------------
-- HEISENBERG TRANSLATIONS ARE EXACT C3^6 TORUS AUTOMORPHISMS
--
-- The 729-point appraisal fibre is exactly X6 = F3^6.  On the periodic
-- adjacency each Heisenberg translation is a coordinate-wise cyclic shift and
-- preserves every torus edge.  The earlier obstruction occurs only after
-- restricting to the non-periodic P3^6 observational box.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Heisenberg
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Carrier
import DASHI.Moonshine.Base369HeisenbergTranslationGridObstructionExact as Translation
import DASHI.Moonshine.Base369PeriodicTernaryTorusPathRestrictionBidiExact as Torus

------------------------------------------------------------------------
-- 1. Cyclic increment transported to SSP trits.
------------------------------------------------------------------------

cyclicIncrement : SSP.SSPTrit → SSP.SSPTrit
cyclicIncrement SSP.sspNegOne = SSP.sspZero
cyclicIncrement SSP.sspZero = SSP.sspPosOne
cyclicIncrement SSP.sspPosOne = SSP.sspNegOne

heisenbergIncrementMatchesCyclicIncrement :
  (t : SSP.SSPTrit) →
  Carrier.tritToSSP (Heisenberg.increment (Carrier.sspToTrit t))
  ≡ cyclicIncrement t
heisenbergIncrementMatchesCyclicIncrement SSP.sspNegOne = refl
heisenbergIncrementMatchesCyclicIncrement SSP.sspZero = refl
heisenbergIncrementMatchesCyclicIncrement SSP.sspPosOne = refl

cyclicIncrementPreservesStep :
  ∀ {a b} → Torus.CyclicTritStep a b →
  Torus.CyclicTritStep (cyclicIncrement a) (cyclicIncrement b)
cyclicIncrementPreservesStep Torus.negToZero = Torus.zeroToPos
cyclicIncrementPreservesStep Torus.zeroToNeg = Torus.posToZero
cyclicIncrementPreservesStep Torus.zeroToPos = Torus.posToNegWrap
cyclicIncrementPreservesStep Torus.posToZero = Torus.negToPosWrap
cyclicIncrementPreservesStep Torus.posToNegWrap = Torus.negToZero
cyclicIncrementPreservesStep Torus.negToPosWrap = Torus.zeroToNeg

------------------------------------------------------------------------
-- 2. Six-coordinate periodic appraisal-fibre adjacency.
------------------------------------------------------------------------

data PeriodicFibreAdjacent :
  Geometry.AppraisalFibrePoint → Geometry.AppraisalFibrePoint → Set where
  edgeA0 : ∀ {a0 a1 a2 a0' b0 b1 b2} → Torus.CyclicTritStep a0 a0' →
    PeriodicFibreAdjacent
      (Geometry.appraisalFibrePoint
        (Geometry.ternary27Point a0 a1 a2)
        (Geometry.ternary27Point b0 b1 b2))
      (Geometry.appraisalFibrePoint
        (Geometry.ternary27Point a0' a1 a2)
        (Geometry.ternary27Point b0 b1 b2))
  edgeA1 : ∀ {a0 a1 a2 a1' b0 b1 b2} → Torus.CyclicTritStep a1 a1' →
    PeriodicFibreAdjacent
      (Geometry.appraisalFibrePoint
        (Geometry.ternary27Point a0 a1 a2)
        (Geometry.ternary27Point b0 b1 b2))
      (Geometry.appraisalFibrePoint
        (Geometry.ternary27Point a0 a1' a2)
        (Geometry.ternary27Point b0 b1 b2))
  edgeA2 : ∀ {a0 a1 a2 a2' b0 b1 b2} → Torus.CyclicTritStep a2 a2' →
    PeriodicFibreAdjacent
      (Geometry.appraisalFibrePoint
        (Geometry.ternary27Point a0 a1 a2)
        (Geometry.ternary27Point b0 b1 b2))
      (Geometry.appraisalFibrePoint
        (Geometry.ternary27Point a0 a1 a2')
        (Geometry.ternary27Point b0 b1 b2))
  edgeB0 : ∀ {a0 a1 a2 b0 b1 b2 b0'} → Torus.CyclicTritStep b0 b0' →
    PeriodicFibreAdjacent
      (Geometry.appraisalFibrePoint
        (Geometry.ternary27Point a0 a1 a2)
        (Geometry.ternary27Point b0 b1 b2))
      (Geometry.appraisalFibrePoint
        (Geometry.ternary27Point a0 a1 a2)
        (Geometry.ternary27Point b0' b1 b2))
  edgeB1 : ∀ {a0 a1 a2 b0 b1 b2 b1'} → Torus.CyclicTritStep b1 b1' →
    PeriodicFibreAdjacent
      (Geometry.appraisalFibrePoint
        (Geometry.ternary27Point a0 a1 a2)
        (Geometry.ternary27Point b0 b1 b2))
      (Geometry.appraisalFibrePoint
        (Geometry.ternary27Point a0 a1 a2)
        (Geometry.ternary27Point b0 b1' b2))
  edgeB2 : ∀ {a0 a1 a2 b0 b1 b2 b2'} → Torus.CyclicTritStep b2 b2' →
    PeriodicFibreAdjacent
      (Geometry.appraisalFibrePoint
        (Geometry.ternary27Point a0 a1 a2)
        (Geometry.ternary27Point b0 b1 b2))
      (Geometry.appraisalFibrePoint
        (Geometry.ternary27Point a0 a1 a2)
        (Geometry.ternary27Point b0 b1 b2'))

------------------------------------------------------------------------
-- 3. Coordinate-wise geometric periodic shift.
------------------------------------------------------------------------

periodicShiftFibre :
  Heisenberg.Axis6 → Geometry.AppraisalFibrePoint → Geometry.AppraisalFibrePoint
periodicShiftFibre Heisenberg.axis0
  (Geometry.appraisalFibrePoint (Geometry.ternary27Point a0 a1 a2) b) =
  Geometry.appraisalFibrePoint (Geometry.ternary27Point (cyclicIncrement a0) a1 a2) b
periodicShiftFibre Heisenberg.axis1
  (Geometry.appraisalFibrePoint (Geometry.ternary27Point a0 a1 a2) b) =
  Geometry.appraisalFibrePoint (Geometry.ternary27Point a0 (cyclicIncrement a1) a2) b
periodicShiftFibre Heisenberg.axis2
  (Geometry.appraisalFibrePoint (Geometry.ternary27Point a0 a1 a2) b) =
  Geometry.appraisalFibrePoint (Geometry.ternary27Point a0 a1 (cyclicIncrement a2)) b
periodicShiftFibre Heisenberg.axis3
  (Geometry.appraisalFibrePoint a (Geometry.ternary27Point b0 b1 b2)) =
  Geometry.appraisalFibrePoint a (Geometry.ternary27Point (cyclicIncrement b0) b1 b2)
periodicShiftFibre Heisenberg.axis4
  (Geometry.appraisalFibrePoint a (Geometry.ternary27Point b0 b1 b2)) =
  Geometry.appraisalFibrePoint a (Geometry.ternary27Point b0 (cyclicIncrement b1) b2)
periodicShiftFibre Heisenberg.axis5
  (Geometry.appraisalFibrePoint a (Geometry.ternary27Point b0 b1 b2)) =
  Geometry.appraisalFibrePoint a (Geometry.ternary27Point b0 b1 (cyclicIncrement b2))

heisenbergTranslationEqualsPeriodicShift :
  (axis : Heisenberg.Axis6) → (f : Geometry.AppraisalFibrePoint) →
  Translation.heisenbergTranslateFibre axis f ≡ periodicShiftFibre axis f
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis0
  (Geometry.appraisalFibrePoint (Geometry.ternary27Point SSP.sspNegOne a1 a2) b) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis0
  (Geometry.appraisalFibrePoint (Geometry.ternary27Point SSP.sspZero a1 a2) b) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis0
  (Geometry.appraisalFibrePoint (Geometry.ternary27Point SSP.sspPosOne a1 a2) b) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis1
  (Geometry.appraisalFibrePoint (Geometry.ternary27Point a0 SSP.sspNegOne a2) b) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis1
  (Geometry.appraisalFibrePoint (Geometry.ternary27Point a0 SSP.sspZero a2) b) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis1
  (Geometry.appraisalFibrePoint (Geometry.ternary27Point a0 SSP.sspPosOne a2) b) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis2
  (Geometry.appraisalFibrePoint (Geometry.ternary27Point a0 a1 SSP.sspNegOne) b) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis2
  (Geometry.appraisalFibrePoint (Geometry.ternary27Point a0 a1 SSP.sspZero) b) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis2
  (Geometry.appraisalFibrePoint (Geometry.ternary27Point a0 a1 SSP.sspPosOne) b) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis3
  (Geometry.appraisalFibrePoint a (Geometry.ternary27Point SSP.sspNegOne b1 b2)) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis3
  (Geometry.appraisalFibrePoint a (Geometry.ternary27Point SSP.sspZero b1 b2)) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis3
  (Geometry.appraisalFibrePoint a (Geometry.ternary27Point SSP.sspPosOne b1 b2)) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis4
  (Geometry.appraisalFibrePoint a (Geometry.ternary27Point b0 SSP.sspNegOne b2)) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis4
  (Geometry.appraisalFibrePoint a (Geometry.ternary27Point b0 SSP.sspZero b2)) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis4
  (Geometry.appraisalFibrePoint a (Geometry.ternary27Point b0 SSP.sspPosOne b2)) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis5
  (Geometry.appraisalFibrePoint a (Geometry.ternary27Point b0 b1 SSP.sspNegOne)) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis5
  (Geometry.appraisalFibrePoint a (Geometry.ternary27Point b0 b1 SSP.sspZero)) = refl
heisenbergTranslationEqualsPeriodicShift Heisenberg.axis5
  (Geometry.appraisalFibrePoint a (Geometry.ternary27Point b0 b1 SSP.sspPosOne)) = refl

------------------------------------------------------------------------
-- 4. Any cyclic coordinate shift preserves periodic adjacency.
------------------------------------------------------------------------

shiftAxis0PreservesPeriodicAdjacency :
  ∀ {f g} → PeriodicFibreAdjacent f g →
  PeriodicFibreAdjacent
    (periodicShiftFibre Heisenberg.axis0 f)
    (periodicShiftFibre Heisenberg.axis0 g)
shiftAxis0PreservesPeriodicAdjacency (edgeA0 step) = edgeA0 (cyclicIncrementPreservesStep step)
shiftAxis0PreservesPeriodicAdjacency (edgeA1 step) = edgeA1 step
shiftAxis0PreservesPeriodicAdjacency (edgeA2 step) = edgeA2 step
shiftAxis0PreservesPeriodicAdjacency (edgeB0 step) = edgeB0 step
shiftAxis0PreservesPeriodicAdjacency (edgeB1 step) = edgeB1 step
shiftAxis0PreservesPeriodicAdjacency (edgeB2 step) = edgeB2 step

-- The remaining axes follow by the same coordinate-local calculation.
shiftAxis1PreservesPeriodicAdjacency :
  ∀ {f g} → PeriodicFibreAdjacent f g →
  PeriodicFibreAdjacent
    (periodicShiftFibre Heisenberg.axis1 f)
    (periodicShiftFibre Heisenberg.axis1 g)
shiftAxis1PreservesPeriodicAdjacency (edgeA0 step) = edgeA0 step
shiftAxis1PreservesPeriodicAdjacency (edgeA1 step) = edgeA1 (cyclicIncrementPreservesStep step)
shiftAxis1PreservesPeriodicAdjacency (edgeA2 step) = edgeA2 step
shiftAxis1PreservesPeriodicAdjacency (edgeB0 step) = edgeB0 step
shiftAxis1PreservesPeriodicAdjacency (edgeB1 step) = edgeB1 step
shiftAxis1PreservesPeriodicAdjacency (edgeB2 step) = edgeB2 step

shiftAxis2PreservesPeriodicAdjacency :
  ∀ {f g} → PeriodicFibreAdjacent f g → PeriodicFibreAdjacent
    (periodicShiftFibre Heisenberg.axis2 f) (periodicShiftFibre Heisenberg.axis2 g)
shiftAxis2PreservesPeriodicAdjacency (edgeA0 step) = edgeA0 step
shiftAxis2PreservesPeriodicAdjacency (edgeA1 step) = edgeA1 step
shiftAxis2PreservesPeriodicAdjacency (edgeA2 step) = edgeA2 (cyclicIncrementPreservesStep step)
shiftAxis2PreservesPeriodicAdjacency (edgeB0 step) = edgeB0 step
shiftAxis2PreservesPeriodicAdjacency (edgeB1 step) = edgeB1 step
shiftAxis2PreservesPeriodicAdjacency (edgeB2 step) = edgeB2 step

shiftAxis3PreservesPeriodicAdjacency :
  ∀ {f g} → PeriodicFibreAdjacent f g → PeriodicFibreAdjacent
    (periodicShiftFibre Heisenberg.axis3 f) (periodicShiftFibre Heisenberg.axis3 g)
shiftAxis3PreservesPeriodicAdjacency (edgeA0 step) = edgeA0 step
shiftAxis3PreservesPeriodicAdjacency (edgeA1 step) = edgeA1 step
shiftAxis3PreservesPeriodicAdjacency (edgeA2 step) = edgeA2 step
shiftAxis3PreservesPeriodicAdjacency (edgeB0 step) = edgeB0 (cyclicIncrementPreservesStep step)
shiftAxis3PreservesPeriodicAdjacency (edgeB1 step) = edgeB1 step
shiftAxis3PreservesPeriodicAdjacency (edgeB2 step) = edgeB2 step

shiftAxis4PreservesPeriodicAdjacency :
  ∀ {f g} → PeriodicFibreAdjacent f g → PeriodicFibreAdjacent
    (periodicShiftFibre Heisenberg.axis4 f) (periodicShiftFibre Heisenberg.axis4 g)
shiftAxis4PreservesPeriodicAdjacency (edgeA0 step) = edgeA0 step
shiftAxis4PreservesPeriodicAdjacency (edgeA1 step) = edgeA1 step
shiftAxis4PreservesPeriodicAdjacency (edgeA2 step) = edgeA2 step
shiftAxis4PreservesPeriodicAdjacency (edgeB0 step) = edgeB0 step
shiftAxis4PreservesPeriodicAdjacency (edgeB1 step) = edgeB1 (cyclicIncrementPreservesStep step)
shiftAxis4PreservesPeriodicAdjacency (edgeB2 step) = edgeB2 step

shiftAxis5PreservesPeriodicAdjacency :
  ∀ {f g} → PeriodicFibreAdjacent f g → PeriodicFibreAdjacent
    (periodicShiftFibre Heisenberg.axis5 f) (periodicShiftFibre Heisenberg.axis5 g)
shiftAxis5PreservesPeriodicAdjacency (edgeA0 step) = edgeA0 step
shiftAxis5PreservesPeriodicAdjacency (edgeA1 step) = edgeA1 step
shiftAxis5PreservesPeriodicAdjacency (edgeA2 step) = edgeA2 step
shiftAxis5PreservesPeriodicAdjacency (edgeB0 step) = edgeB0 step
shiftAxis5PreservesPeriodicAdjacency (edgeB1 step) = edgeB1 step
shiftAxis5PreservesPeriodicAdjacency (edgeB2 step) = edgeB2 (cyclicIncrementPreservesStep step)

heisenbergTranslationPreservesPeriodicAdjacency :
  (axis : Heisenberg.Axis6) → ∀ {f g} → PeriodicFibreAdjacent f g →
  PeriodicFibreAdjacent
    (Translation.heisenbergTranslateFibre axis f)
    (Translation.heisenbergTranslateFibre axis g)
heisenbergTranslationPreservesPeriodicAdjacency Heisenberg.axis0 {f} {g} edge
  rewrite heisenbergTranslationEqualsPeriodicShift Heisenberg.axis0 f
        | heisenbergTranslationEqualsPeriodicShift Heisenberg.axis0 g =
  shiftAxis0PreservesPeriodicAdjacency edge
heisenbergTranslationPreservesPeriodicAdjacency Heisenberg.axis1 {f} {g} edge
  rewrite heisenbergTranslationEqualsPeriodicShift Heisenberg.axis1 f
        | heisenbergTranslationEqualsPeriodicShift Heisenberg.axis1 g =
  shiftAxis1PreservesPeriodicAdjacency edge
heisenbergTranslationPreservesPeriodicAdjacency Heisenberg.axis2 {f} {g} edge
  rewrite heisenbergTranslationEqualsPeriodicShift Heisenberg.axis2 f
        | heisenbergTranslationEqualsPeriodicShift Heisenberg.axis2 g =
  shiftAxis2PreservesPeriodicAdjacency edge
heisenbergTranslationPreservesPeriodicAdjacency Heisenberg.axis3 {f} {g} edge
  rewrite heisenbergTranslationEqualsPeriodicShift Heisenberg.axis3 f
        | heisenbergTranslationEqualsPeriodicShift Heisenberg.axis3 g =
  shiftAxis3PreservesPeriodicAdjacency edge
heisenbergTranslationPreservesPeriodicAdjacency Heisenberg.axis4 {f} {g} edge
  rewrite heisenbergTranslationEqualsPeriodicShift Heisenberg.axis4 f
        | heisenbergTranslationEqualsPeriodicShift Heisenberg.axis4 g =
  shiftAxis4PreservesPeriodicAdjacency edge
heisenbergTranslationPreservesPeriodicAdjacency Heisenberg.axis5 {f} {g} edge
  rewrite heisenbergTranslationEqualsPeriodicShift Heisenberg.axis5 f
        | heisenbergTranslationEqualsPeriodicShift Heisenberg.axis5 g =
  shiftAxis5PreservesPeriodicAdjacency edge

------------------------------------------------------------------------
-- 5. BIDI boundary.
------------------------------------------------------------------------

record PeriodicHeisenbergEquivarianceBoundary : Set where
  constructor periodicHeisenbergEquivarianceBoundary
  field
    allSixTranslationsArePeriodicGraphAutomorphisms : Bool
    allSixTranslationsArePathGraphAutomorphisms : Bool
    wraparoundExplainsFailureDownstairs : Bool
    carrierAndPeriodicTranslationIntertwiningEstablished : Bool
    modulationObservableIntertwiningEstablishedHere : Bool
    fullMonsterNormalizerActionEstablishedHere : Bool

canonicalPeriodicHeisenbergEquivarianceBoundary : PeriodicHeisenbergEquivarianceBoundary
canonicalPeriodicHeisenbergEquivarianceBoundary =
  periodicHeisenbergEquivarianceBoundary true false true true false false
