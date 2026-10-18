{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650ExternalTotalizationNonzeroWeldRound671Exact where

------------------------------------------------------------------------
-- ROUND671 / RAW WEIGHTED EXTERNAL COMMUTATOR -> R630 TOTAL CARRIER ON p != 0
--
-- R670 closes the swap-invariant weighted external product-rule reindexing on
-- the raw weighted external commutator.  R630 is the canonical total carrier
-- used by R631/R636/R637 and deliberately has an explicit p = 0 branch.
--
-- PhysicalTriadIncidence itself does NOT assert p != 0.  Therefore we must not
-- erase R630's zero branch globally.
--
-- On an incidence carrying an actual NonZeroMode(p) witness, however, the
-- executable p=0 branch is impossible and the raw doubled weighted external
-- commutator is definitionally the R630 total exhaustive carrier.  Doubling
-- gives the corresponding nested-cell weld.
--
-- This is the strongest assumption-free-safe bridge available at this layer:
-- exact on p != 0, explicit totalization at p = 0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNExternalWeightedSlotCommutatorRound629Exact as R629
import DASHI.Physics.Closure.NSTriadKNExternalWeightedSlotCommutatorTotalRound630Exact as R630

module NonzeroWeld
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Comm =
    R629.ExternalSlotCommutator629 W S L H system velocityTransverse

  module Total =
    R630.TotalExternalCommutator630 W S L H system velocityTransverse

  rawWeightedDoubleExternalCommutator :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  rawWeightedDoubleExternalCommutator tau =
    C3.complex3Scale (R294.weight W tau)
      (C3.complex3Add
        (Comm.Ext.externalCommutatorCell tau)
        (Comm.Ext.externalCommutatorCell tau))

  rawEqualsTotalOnPNonzero :
    (tau : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.p tau) →
    rawWeightedDoubleExternalCommutator tau
    ≡ Total.totalExternalExhaustiveCommutator tau
  rawEqualsTotalOnPNonzero tau pNonzero
      with Output.modeEqual (Physical.p tau) Z3.zeroMode in decision
  ... | true =
    ⊥-elim
      (Z3.notZero pNonzero (Output.modeEqualSound decision))
  ... | false = refl

  rawWeightedNestedExternalCommutator :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  rawWeightedNestedExternalCommutator tau =
    C3.complex3Add
      (rawWeightedDoubleExternalCommutator tau)
      (rawWeightedDoubleExternalCommutator tau)

  rawNestedEqualsTotalOnPNonzero :
    (tau : Physical.PhysicalTriadIncidence) →
    (pNonzero : Z3.NonZeroMode (Physical.p tau)) →
    rawWeightedNestedExternalCommutator tau
    ≡ Total.totalExternalNestedCommutator tau
  rawNestedEqualsTotalOnPNonzero tau pNonzero =
    cong₂ C3.complex3Add
      (rawEqualsTotalOnPNonzero tau pNonzero)
      (rawEqualsTotalOnPNonzero tau pNonzero)

------------------------------------------------------------------------
-- Status / zero-branch firewall.
------------------------------------------------------------------------

round671RawTotalExternalWeldOnPNonzeroClosed : Bool
round671RawTotalExternalWeldOnPNonzeroClosed = true

round671RawTotalNestedWeldOnPNonzeroClosed : Bool
round671RawTotalNestedWeldOnPNonzeroClosed = true

round671PhysicalTriadIncidenceGloballySuppliesPNonzero : Bool
round671PhysicalTriadIncidenceGloballySuppliesPNonzero = false

round671R630ZeroBranchMayBeErasedGlobally : Bool
round671R630ZeroBranchMayBeErasedGlobally = false

round671IntroducesEstimate : Bool
round671IntroducesEstimate = false

round671IntroducesNewClayLeaf : Bool
round671IntroducesNewClayLeaf = false

round671ClayPromotion : Bool
round671ClayPromotion = false

round671RawTotalExternalWeldOnPNonzeroClosedIsTrue :
  round671RawTotalExternalWeldOnPNonzeroClosed ≡ true
round671RawTotalExternalWeldOnPNonzeroClosedIsTrue = refl

round671RawTotalNestedWeldOnPNonzeroClosedIsTrue :
  round671RawTotalNestedWeldOnPNonzeroClosed ≡ true
round671RawTotalNestedWeldOnPNonzeroClosedIsTrue = refl

round671PhysicalTriadIncidenceGloballySuppliesPNonzeroIsFalse :
  round671PhysicalTriadIncidenceGloballySuppliesPNonzero ≡ false
round671PhysicalTriadIncidenceGloballySuppliesPNonzeroIsFalse = refl

round671R630ZeroBranchMayBeErasedGloballyIsFalse :
  round671R630ZeroBranchMayBeErasedGlobally ≡ false
round671R630ZeroBranchMayBeErasedGloballyIsFalse = refl

round671IntroducesEstimateIsFalse :
  round671IntroducesEstimate ≡ false
round671IntroducesEstimateIsFalse = refl

round671IntroducesNewClayLeafIsFalse :
  round671IntroducesNewClayLeaf ≡ false
round671IntroducesNewClayLeafIsFalse = refl

round671ClayPromotionIsFalse :
  round671ClayPromotion ≡ false
round671ClayPromotionIsFalse = refl
