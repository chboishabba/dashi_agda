module DASHI.Physics.Closure.NSTriadKNCollarHeatNestedSameOutputWeldExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b2d / COLLAR -> EXISTING SIGNED HEAT-NESTED CARRIER
--
-- The exact-shell collar is already an R98 Boolean packet selector.  R419
-- proves that the R329/R336 heat-nested outer incidence is literally the SAME
-- R98 packet cell and that `sameFinalOutput` preserves any selector bit.
--
-- This owner merely specializes that theorem to the exact collar selector.
-- It introduces no proxy incidence, no re-enumeration and no estimate.
-- Therefore the next collar theorem is quantitatively sharp:
--
--   same-scale signed collar payment on the existing heat/companion carrier.
--
-- In particular, this file does NOT claim the R423 cutoff-uniform signed
-- companion budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPreTTStarAdapterRound336Exact as R336
import DASHI.Physics.Closure.NSTriadKNHeatNestedOuterPacketCarrierRound419Exact as R419
import DASHI.Physics.Closure.NSTriadKNUpperShellCollarRemoteSplitExact as Collar

F : C3.RealField _
F = Rational.rationalRealField

collarNestedOuterPacketPower :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (O : Leray.RationalInverseNormOrder E I) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (shell : Nat) →
  R329.StrongLowLiteralNestedCell E I O system S L H W →
  ℚ
collarNestedOuterPacketPower E I O system S L H W shell =
  R419.nestedOuterPacketPower
    E I O system S L H W (Collar.collarShellPacket shell)

collarNestedOuterPacketPowerIsLiteralR98OnSameOuter :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (O : Leray.RationalInverseNormOrder E I) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (shell : Nat) →
  (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  collarNestedOuterPacketPower E I O system S L H W shell C
  ≡ R419.nestedOuterPacketPower
      E I O system S L H W (Collar.collarShellPacket shell) C
collarNestedOuterPacketPowerIsLiteralR98OnSameOuter
    E I O system S L H W shell C = refl

sameFinalOutputImpliesSameCollarSelectorBit :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (O : Leray.RationalInverseNormOrder E I) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (shell : Nat) →
  (P : R336.HeatWeightedNestedPairwiseOverlap E I O system S L H W) →
  Collar.collarShellPacket shell
      (Physical.k (R329.outer (R336.left P)))
  ≡ Collar.collarShellPacket shell
      (Physical.k (R329.outer (R336.right P)))
sameFinalOutputImpliesSameCollarSelectorBit
    E I O system S L H W shell P =
  R419.sameFinalOutputImpliesSamePacketSelectorBit
    E I O system S L H W (Collar.collarShellPacket shell) P

collarUsesSameR98OuterCarrier : Bool
collarUsesSameR98OuterCarrier = true

sameOutputPreservesCollarSelector : Bool
sameOutputPreservesCollarSelector = true

collarQuantitativeSignedBudgetClosed : Bool
collarQuantitativeSignedBudgetClosed = false

collarUsesSameR98OuterCarrierIsTrue :
  collarUsesSameR98OuterCarrier ≡ true
collarUsesSameR98OuterCarrierIsTrue = refl

sameOutputPreservesCollarSelectorIsTrue :
  sameOutputPreservesCollarSelector ≡ true
sameOutputPreservesCollarSelectorIsTrue = refl

collarQuantitativeSignedBudgetClosedIsFalse :
  collarQuantitativeSignedBudgetClosed ≡ false
collarQuantitativeSignedBudgetClosedIsFalse = refl
