module DASHI.Physics.Closure.NSTriadKNUnrestrictedNestedOperatorShellNormalizationRound585Exact where

------------------------------------------------------------------------
-- ROUND585 / NORMALIZE THE UNRESTRICTED NESTED OPERATOR SHELL
--
-- R584 deliberately exposed three outer physical coordinates before choosing
-- an operator-shell semantics.  R573's actual construction resolves the choice:
-- for an outer incidence tau, the nested block enumerates the COMPLETE inner
-- fibre with output exactly p_tau,
--
--   physicalOutputFiber cutoff (p tau),
--
-- and then inserts that block into the outer slot against the spectator q_tau.
-- Thus the source-native block/operator index is the OUTER FORCING LEG p.
--
-- The final output k cannot serve as the cross-shell index on R584 pairs because
-- SameOutputNestedPair584 already requires k_left = k_right.  The q leg remains
-- a useful spectator coordinate, but it is not the index used to select the
-- nested inner output fibre.
--
-- This is a representation normalization, not a decay estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNUnrestrictedNestedSignedOverlapRound584Exact as R584

canonicalNestedOperatorCoordinate585 : R584.OuterOperatorShellCoordinate584
canonicalNestedOperatorCoordinate585 = R584.outerForcing584

canonicalNestedOperatorShell585 :
  Physical.PhysicalTriadIncidence → Nat
canonicalNestedOperatorShell585 tau =
  Shell.shellIndex (Physical.p tau)

canonicalCoordinateComputesForcingShell585 :
  (tau : Physical.PhysicalTriadIncidence) →
  R584.shellAtOuterCoordinate584 canonicalNestedOperatorCoordinate585 tau
  ≡ canonicalNestedOperatorShell585 tau
canonicalCoordinateComputesForcingShell585 tau = refl

finalOutputShellsCoincideOnSameOutputPair585 :
  ∀ {r} {F : DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier.RealField r}
    {E : DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier.IntegerEmbedding F}
    {I : DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier.ModeInverseSquare F E}
    {O : DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras.RationalInverseNormOrder E I}
    {system : DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.FiniteComplex3GalerkinSystem F E I}
    {S : DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure.HelicalModeScalars F}
    {L : DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure.PeriodicHelicalProjectorLaws F E I S}
    {H : DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact.HelicalHalfCalibration S}
    {W : DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact.SwapInvariantCellWeight F}
    {velocityTransverse :
      (mode : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode) →
      DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure.Transverse E mode
        (DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.velocity system mode)} →
  (pair :
    R584.UnrestrictedNested584.SameOutputNestedPair584
      E I O system S L H W velocityTransverse) →
  Shell.shellIndex
    (Physical.k
      (R584.UnrestrictedNested584.left584 E I O system S L H W velocityTransverse pair))
  ≡
  Shell.shellIndex
    (Physical.k
      (R584.UnrestrictedNested584.right584 E I O system S L H W velocityTransverse pair))
finalOutputShellsCoincideOnSameOutputPair585 pair =
  cong Shell.shellIndex
    (R584.UnrestrictedNested584.sameFinalOutput584 pair)

-- The preferred R29 adapter is now normalized to the physical p-shell.
-- No caller supplies shell labels.

round585SourceNativeNestedBlockIndexedByOuterForcing : Bool
round585SourceNativeNestedBlockIndexedByOuterForcing = true

round585FinalOutputRejectedAsCrossShellIndex : Bool
round585FinalOutputRejectedAsCrossShellIndex = true

round585CanonicalOperatorShellCoordinateSelected : Bool
round585CanonicalOperatorShellCoordinateSelected = true

round585SeparationIndexedDecayClosed : Bool
round585SeparationIndexedDecayClosed = false

round585CutoffUniformSeparationSummationClosed : Bool
round585CutoffUniformSeparationSummationClosed = false

round585LeafAClosed : Bool
round585LeafAClosed = false

round585ClayPromotion : Bool
round585ClayPromotion = false

round585CanonicalOperatorShellCoordinateSelectedIsTrue :
  round585CanonicalOperatorShellCoordinateSelected ≡ true
round585CanonicalOperatorShellCoordinateSelectedIsTrue = refl

round585SeparationIndexedDecayClosedIsFalse :
  round585SeparationIndexedDecayClosed ≡ false
round585SeparationIndexedDecayClosedIsFalse = refl

round585ClayPromotionIsFalse : round585ClayPromotion ≡ false
round585ClayPromotionIsFalse = refl
