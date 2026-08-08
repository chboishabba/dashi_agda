module DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaRound26Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Integrate the Round 26 highest-alpha tranche after Round 25 closed physical
-- support.  This round advances three different proof layers without
-- conflating them:
--
-- * finite Galerkin algebra: reality reconstruction, degree-two coordinate
--   syntax, exact difference factorisation and triadwise energy cancellation;
-- * finite critical accounting: a signed weighted shell ledger with explicit
--   HH/LH/HL/CC/Com and cutoff-boundary coordinates;
-- * analytic tax discipline: finite commutator increments, division-free HH
--   normalisation, hysteretic entry charge, named remainder classes and
--   duplicate-free tax ownership.
--
-- The continuum-real Picard-Lindelof instance, cutoff-independent class taxes,
-- strict viscosity margin and Clay theorem remain open.
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
import DASHI.Physics.Closure.NSTriadKNLuoDivisionFreeHHDefectRound26Exact as HH
import DASHI.Physics.Closure.NSTriadKNLuoFiniteTaxAdversarialRegressionRound26Exact as Regression
import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial
import DASHI.Physics.Closure.NSTriadKNLuoHystereticPositiveVariationRound26Exact as Hysteresis
import DASHI.Physics.Closure.NSTriadKNLuoCriticalRemainderClassificationRound26Exact as Remainder

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
    triadwiseEnergyCancellationProved : Bool
    finiteGalerkinGlobalExistenceInstantiated : Bool
    signedCriticalShellLedgerProved : Bool
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
    true true false false
    true false
    true true true false
    true true true true
    false false false false

localODEStillOpen :
  continuumRealLocalODEExistenceInstantiated
    canonicalRound26HighestAlphaBoundary
  ≡ false
localODEStillOpen = refl

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
