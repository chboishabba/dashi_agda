module DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaRound26Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Integrate the Round 26 highest-alpha tranche after Round 25 closed physical
-- support.  This round advances three different proof layers without
-- conflating them:
--
-- * finite Galerkin algebra: reality reconstruction, conjugate transversality,
--   degree-two coordinate syntax, exact difference factorisation and physical
--   triad cancellation;
-- * finite critical accounting: the Round-25 physical five-source fibre is
--   forced into a signed weighted shell ledger with explicit boundaries;
-- * analytic tax discipline: finite commutator increments, division-free HH
--   normalisation, hysteretic entry charge, named remainder classes and
--   duplicate-free tax ownership.
--
-- The finite normed Picard-Lindelof instance, physical time-dependent shell
-- balances, cutoff-independent class taxes, strict viscosity margin and Clay
-- theorem remain open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaClayLemmaLadderRound24Exact as R24
import DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaClayLemmaLadderRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNLuoTriadwiseEnergyCancellationRound26Exact as Energy
import DASHI.Physics.Closure.NSTriadKNLuoFiniteKernelCommutatorRound26Exact as Kernel
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNLuoSignedCriticalLedgerRound26Exact as Ledger
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalSignedShellCellRound26Exact as PhysicalShell
import DASHI.Physics.Closure.NSTriadKNLuoDivisionFreeHHDefectRound26Exact as HH
import DASHI.Physics.Closure.NSTriadKNLuoFiniteTaxAdversarialRegressionRound26Exact as Regression
import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial
import DASHI.Physics.Closure.NSTriadKNLuoHystereticPositiveVariationRound26Exact as Hysteresis
import DASHI.Physics.Closure.NSTriadKNLuoCriticalRemainderClassificationRound26Exact as Remainder
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase

record Round26ExactEvidence : Set₁ where
  field
    triadwiseEnergyCancellation :
      (coordinates : Energy.ResonantTriadEnergyCoordinates) →
      Energy.cyclicTriadEnergyTransfer coordinates ≡ Energy.zeroQ

    finiteKernelCommutator :
      (cells : List Kernel.FiniteKernelTransportCell) →
      Kernel.sumCommutatorCells cells
      ≡ Kernel.sumIncrementCells cells

    finiteFirstMomentScaling :
      (scale : ℚ) →
      (cells : List Kernel.FiniteKernelMomentCell) →
      Kernel.firstMoment (Kernel.scaleMomentCells scale cells)
      ≡ scale * Kernel.firstMoment cells

    duplicateFreeTaxPartition :
      (atoms : List Tax.TaxAtom) →
      Tax.totalTax atoms ≡ Tax.ownedTaxTotal atoms

    signedCriticalLedger :
      (cells : List Ledger.SignedCriticalShellCell) →
      Ledger.sumWeightedEnergyRate cells
        + Ledger.sumWeightedDissipation cells
      ≡
      Ledger.sumWeightedHH cells
        + Ledger.sumWeightedLH cells
        + Ledger.sumWeightedHL cells
        + Ledger.sumWeightedCC cells
        + Ledger.sumWeightedCom cells
        + Ledger.sumWeightedLowerBoundary cells
        + Ledger.sumWeightedUpperBoundary cells

    physicalFiveSourceShellCell :
      (inputs : PhysicalShell.PhysicalSignedShellInputs) →
      Ledger.SignedCriticalShellCell

    physicalFiveSourceShellCellHHMeaning :
      (inputs : PhysicalShell.PhysicalSignedShellInputs) →
      Ledger.HHsource (physicalFiveSourceShellCell inputs)
      ≡ PhysicalShell.physicalHH inputs

    divisionFreeHHProduct :
      (factorisation : HH.DivisionFreeHHDefectFactorisation) →
      HH.defect factorisation * HH.amplitude factorisation
      ≡
      HH.AScale factorisation * HH.AScale factorisation
      * (HH.dissipation factorisation * HH.dissipation factorisation)

    finiteGalerkinDifference :
      (atoms : List Polynomial.GalerkinCoordinateAtom) →
      (state reference : Polynomial.Assignment) →
      Polynomial.evaluateAtoms atoms state
        - Polynomial.evaluateAtoms atoms reference
      ≡ Polynomial.differenceAtoms atoms state reference

    hystereticEntriesPaidByPositiveVariation :
      ∀ {gap} →
      (entries : List (Hysteresis.HystereticEntry gap)) →
      Hysteresis.entryGapCharge entries
      ≤ Hysteresis.entryPositiveVariation entries

    namedRemaindersRecomposeExactly :
      (atoms : List Remainder.RemainderAtom) →
      Remainder.totalRemainder atoms
      ≡
      Remainder.dataRemainder atoms
      + Remainder.integrableRemainder atoms
      + Remainder.smallRemainderTotal atoms
      + Remainder.telescopingRemainder atoms

    earlyAbsoluteValueRegression :
      Regression.one + Regression.negativeOne ≡ Regression.zero

open Round26ExactEvidence public

canonicalRound26ExactEvidence : Round26ExactEvidence
canonicalRound26ExactEvidence = record
  { triadwiseEnergyCancellation =
      Energy.resonantTriadEnergyExchangeCyclicZero
  ; finiteKernelCommutator =
      Kernel.finiteKernelCommutatorIdentity
  ; finiteFirstMomentScaling =
      Kernel.firstMomentScaleLaw
  ; duplicateFreeTaxPartition =
      Tax.duplicateFreeTaxOwnershipExact
  ; signedCriticalLedger =
      Ledger.finiteSignedCriticalLedgerExact
  ; physicalFiveSourceShellCell =
      PhysicalShell.physicalSignedCriticalShellCell
  ; physicalFiveSourceShellCellHHMeaning =
      PhysicalShell.physicalShellCellSourcesAreForced
  ; divisionFreeHHProduct =
      HH.divisionFreeHHProductIdentity
  ; finiteGalerkinDifference =
      Polynomial.finiteGalerkinDifferenceFactorisation
  ; hystereticEntriesPaidByPositiveVariation =
      Hysteresis.hystereticEntryChargeBelowPositiveVariation
  ; namedRemaindersRecomposeExactly =
      Remainder.remainderClassificationExact
  ; earlyAbsoluteValueRegression =
      Regression.signedCancellationExample
  }

record Round26HighestAlphaBoundary : Set where
  constructor round26-highest-alpha-boundary
  field
    round25PhysicalSupportRetained : Bool
    literalQuadraticGalerkinCoordinateAlgebra : Bool
    realityReconstructionByConstruction : Bool
    negativeTransversalityLawInstantiated : Bool
    continuumRealLocalODEExistenceInstantiated : Bool
    physicalTriadEnergyCancellationReused : Bool
    finiteGalerkinGlobalExistenceInstantiated : Bool
    signedCriticalShellLedgerProved : Bool
    physicalFiveSourceSignedShellBridgeProved : Bool
    physicalTimeDependentShellBalancesInstantiated : Bool
    lowTransportPrincipalCancellationProved : Bool
    finiteKernelCommutatorIdentityProved : Bool
    cutoffIndependentCommutatorTaxProved : Bool
    divisionFreeHHNormalisationProved : Bool
    hystereticEntryChargeProved : Bool
    namedRemainderClassificationProved : Bool
    duplicateFreeTaxOwnershipProved : Bool
    classwiseCutoffUniformTaxesProved : Bool
    strictTotalViscosityMarginProved : Bool
    shellAndGalerkinLimitsProved : Bool
    unconditionalClayTheoremPromoted : Bool

open Round26HighestAlphaBoundary public

canonicalRound26HighestAlphaBoundary : Round26HighestAlphaBoundary
canonicalRound26HighestAlphaBoundary =
  round26-highest-alpha-boundary
    true
    true true true false
    true false
    true true false
    true true false
    true true true true
    false false false false

negativeTransversalityClosed :
  negativeTransversalityLawInstantiated
    canonicalRound26HighestAlphaBoundary
  ≡ true
negativeTransversalityClosed = refl

localODEStillOpen :
  continuumRealLocalODEExistenceInstantiated
    canonicalRound26HighestAlphaBoundary
  ≡ false
localODEStillOpen = refl

physicalShellEvolutionStillOpen :
  physicalTimeDependentShellBalancesInstantiated
    canonicalRound26HighestAlphaBoundary
  ≡ false
physicalShellEvolutionStillOpen = refl

finiteGlobalExistenceStillOpen :
  finiteGalerkinGlobalExistenceInstantiated
    canonicalRound26HighestAlphaBoundary
  ≡ false
finiteGlobalExistenceStillOpen = refl

uniformTaxesStillOpen :
  classwiseCutoffUniformTaxesProved
    canonicalRound26HighestAlphaBoundary
  ≡ false
uniformTaxesStillOpen = refl

strictMarginStillOpen :
  strictTotalViscosityMarginProved
    canonicalRound26HighestAlphaBoundary
  ≡ false
strictMarginStillOpen = refl

clayPromotionStillFalse :
  unconditionalClayTheoremPromoted
    canonicalRound26HighestAlphaBoundary
  ≡ false
clayPromotionStillFalse = refl

round25Ladder : R24.HighestAlphaClayLemmaLadder
round25Ladder = R25.canonicalHighestAlphaClayLemmaLadderRound25
