module DASHI.Physics.Closure.NSTriadKNExternalSharedModeAntisymmetryDefectRound114Exact where

------------------------------------------------------------------------
-- ROUND114 / EXACT ANTISYMMETRY-DEFECT DECOMPOSITION
--
-- Round113 showed that an exactly antisymmetric shared-mode pair gives the
-- desired multiplier difference.  Round114 removes the binary all-or-nothing
-- bottleneck: for an arbitrary paired transfer define the antisymmetry defect
--
--   R = T_right + T_left.
--
-- Then identically
--
--   w_left T_left + w_right T_right
--     = (w_left - w_right) T_left + w_right R.
--
-- Hence every physical cross-triad reindex, whether perfectly antisymmetric or
-- not, splits into the mature commutator term plus ONE honest remainder.  Exact
-- antisymmetry is the special case R = 0.  This is the correct algebraic target
-- for the physical Waleffe reindex and prevents any hidden replacement of the
-- true network functional by the old commutator functional.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNExternalSharedModeWeightedFluxRound113Exact as R113

antisymmetryDefect :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F
antisymmetryDefect leftTransfer rightTransfer =
  C3.complexAdd rightTransfer leftTransfer

weightedDefect :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F
weightedDefect rightWeight defect =
  C3.complexMultiply rightWeight defect

commutatorPlusDefect :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F →
  C3.Complex F → C3.Complex F → C3.Complex F
commutatorPlusDefect wLeft wRight leftTransfer defect =
  C3.complexAdd
    (R113.weightDifferenceTimes wLeft wRight leftTransfer)
    (weightedDefect wRight defect)

weightedPairIsMultiplierDifferencePlusAntisymmetryDefect :
  ∀ {r} {F : C3.RealField r}
    (wLeft wRight leftTransfer rightTransfer : C3.Complex F) →
  R113.weightedPair wLeft wRight leftTransfer rightTransfer
  ≡ commutatorPlusDefect
      wLeft wRight leftTransfer
      (antisymmetryDefect leftTransfer rightTransfer)
weightedPairIsMultiplierDifferencePlusAntisymmetryDefect
    {F = F} wLeft wRight leftTransfer rightTransfer =
  R.solve 4
    (λ wl wr tl tr →
      ((wl R.⊗ tl) R.⊕ (wr R.⊗ tr))
      R.⊜
      (((wl R.⊕ (R.⊝ wr)) R.⊗ tl)
        R.⊕ (wr R.⊗ (tr R.⊕ tl))))
    refl wLeft wRight leftTransfer rightTransfer
  where module R = Ring.Solver F

antisymmetricPairHasZeroDefect :
  ∀ {r} {F : C3.RealField r}
    (transfer : C3.Complex F) →
  antisymmetryDefect transfer (C3.complexNegate transfer)
  ≡ C3.complexZero F
antisymmetricPairHasZeroDefect {F = F} transfer =
  R.solve 1
    (λ t → ((R.⊝ t) R.⊕ t) R.⊜ R.0#)
    refl transfer
  where module R = Ring.Solver F

zeroDefectCollapsesToMultiplierDifference :
  ∀ {r} {F : C3.RealField r}
    (wLeft wRight transfer : C3.Complex F) →
  commutatorPlusDefect
    wLeft wRight transfer (C3.complexZero F)
  ≡ R113.weightDifferenceTimes wLeft wRight transfer
zeroDefectCollapsesToMultiplierDifference {F = F} wLeft wRight transfer =
  R.solve 3
    (λ wl wr t →
      (((wl R.⊕ (R.⊝ wr)) R.⊗ t)
        R.⊕ (wr R.⊗ R.0#))
      R.⊜ ((wl R.⊕ (R.⊝ wr)) R.⊗ t))
    refl wLeft wRight transfer
  where module R = Ring.Solver F

record SharedModeReindexWithDefect
    {r} (F : C3.RealField r) : Set r where
  field
    leftWeight rightWeight : C3.Complex F
    leftTransfer rightTransfer : C3.Complex F

open SharedModeReindexWithDefect public

reindexDefect :
  ∀ {r} {F : C3.RealField r} →
  SharedModeReindexWithDefect F → C3.Complex F
reindexDefect X = antisymmetryDefect (leftTransfer X) (rightTransfer X)

reindexedWeightedFlux :
  ∀ {r} {F : C3.RealField r} →
  SharedModeReindexWithDefect F → C3.Complex F
reindexedWeightedFlux X =
  R113.weightedPair
    (leftWeight X) (rightWeight X)
    (leftTransfer X) (rightTransfer X)

reindexedCommutatorPart :
  ∀ {r} {F : C3.RealField r} →
  SharedModeReindexWithDefect F → C3.Complex F
reindexedCommutatorPart X =
  R113.weightDifferenceTimes
    (leftWeight X) (rightWeight X) (leftTransfer X)

reindexedRemainderPart :
  ∀ {r} {F : C3.RealField r} →
  SharedModeReindexWithDefect F → C3.Complex F
reindexedRemainderPart X =
  weightedDefect (rightWeight X) (reindexDefect X)

physicalReindexShapeAlwaysSplitsIntoCommutatorPlusDefect :
  ∀ {r} {F : C3.RealField r}
    (X : SharedModeReindexWithDefect F) →
  reindexedWeightedFlux X
  ≡ C3.complexAdd (reindexedCommutatorPart X) (reindexedRemainderPart X)
physicalReindexShapeAlwaysSplitsIntoCommutatorPlusDefect X =
  weightedPairIsMultiplierDifferencePlusAntisymmetryDefect
    (leftWeight X) (rightWeight X)
    (leftTransfer X) (rightTransfer X)

round114ExactAntisymmetryDefectDecompositionClosed : Bool
round114ExactAntisymmetryDefectDecompositionClosed = true

round114PhysicalExternalCrossTriadDefectIdentifiedOnActualWaleffeCells : Bool
round114PhysicalExternalCrossTriadDefectIdentifiedOnActualWaleffeCells = false

round114ExactAntisymmetryDefectDecompositionClosedIsTrue :
  round114ExactAntisymmetryDefectDecompositionClosed ≡ true
round114ExactAntisymmetryDefectDecompositionClosedIsTrue = refl

round114PhysicalExternalCrossTriadDefectIdentifiedOnActualWaleffeCellsIsFalse :
  round114PhysicalExternalCrossTriadDefectIdentifiedOnActualWaleffeCells ≡ false
round114PhysicalExternalCrossTriadDefectIdentifiedOnActualWaleffeCellsIsFalse = refl
