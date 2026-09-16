module DASHI.Physics.Closure.NSTriadKNUnrestrictedNestedOperatorShellNormalizationRound585Exact where

------------------------------------------------------------------------
-- ROUND585 / NORMALIZE THE UNRESTRICTED NESTED OPERATOR SHELL
--
-- R573 constructs each nested block by enumerating the complete inner fibre
-- with output p_tau and then inserts that block into the outer slot against
-- q_tau.  Therefore the source-native block/operator index is the OUTER
-- FORCING LEG p.  The final output k cannot distinguish two R584 cells paired
-- on the same final output.
--
-- This is representation normalization only; no decay estimate is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNUnrestrictedNestedSignedOverlapRound584Exact as R584

canonicalNestedOperatorCoordinate585 : R584.OuterOperatorShellCoordinate584
canonicalNestedOperatorCoordinate585 = R584.outerForcing584

canonicalNestedOperatorShell585 : Physical.PhysicalTriadIncidence → Nat
canonicalNestedOperatorShell585 tau = Shell.shellIndex (Physical.p tau)

canonicalCoordinateComputesForcingShell585 :
  (tau : Physical.PhysicalTriadIncidence) →
  R584.shellAtOuterCoordinate584 canonicalNestedOperatorCoordinate585 tau
  ≡ canonicalNestedOperatorShell585 tau
canonicalCoordinateComputesForcingShell585 tau = refl

module SameOutputNormalization585
    {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module U = R584.UnrestrictedNested584 E I O system S L H W velocityTransverse

  finalOutputShellsCoincideOnSameOutputPair585 :
    (pair : U.SameOutputNestedPair584) →
    Shell.shellIndex (Physical.k (U.left584 pair))
    ≡ Shell.shellIndex (Physical.k (U.right584 pair))
  finalOutputShellsCoincideOnSameOutputPair585 pair =
    cong Shell.shellIndex (U.sameFinalOutput584 pair)

  canonicalLeftShell585 : U.SameOutputNestedPair584 → Nat
  canonicalLeftShell585 pair =
    U.leftShell584 canonicalNestedOperatorCoordinate585 pair

  canonicalRightShell585 : U.SameOutputNestedPair584 → Nat
  canonicalRightShell585 pair =
    U.rightShell584 canonicalNestedOperatorCoordinate585 pair

  canonicalSeparation585 : U.SameOutputNestedPair584 → Nat
  canonicalSeparation585 pair =
    U.shellSeparation584 canonicalNestedOperatorCoordinate585 pair

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
