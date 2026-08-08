module DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaClayLemmaLadderRound25Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Refine the Round 24 L0--L23 ladder after proving the literal finite carrier
-- certificate and the exhaustive physical five-class support theorem.
--
-- L4 is now checked exact: every actual cutoff Z^3 resonant triad is assigned
-- uniquely to LH, HL, HH or CC, the differentiated commutator is the fifth
-- class, low-low-to-far-high is impossible, and the resulting rational
-- convolution sum recomposes exactly with no unnamed remainder.
--
-- L3 remains one aggregate physical producer only because the continuum-real
-- finite-dimensional ODE existence and propagation of the reality/transverse
-- constraints have not yet been instantiated.  Its combinatorial, Fourier,
-- Leray and coefficient-identification subclauses are now checked.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; _+_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaClayLemmaLadderRound24Exact as R24
import DASHI.Physics.Closure.NSTriadKNLuoLiteralGalerkinCarrierRound25Exact as Carrier
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSumRound25Exact as Sum

open R24 using
  ( LemmaState
  ; exactTarget
  ; checkedExact
  ; checkedReducer
  ; physicalProducerOpen
  ; HighestAlphaClayLemmaLadder
  ; highestAlphaClayLemmaLadder
  ; highestAlphaPathInputsGiveLiteralClayB
  )

canonicalHighestAlphaClayLemmaLadderRound25 :
  HighestAlphaClayLemmaLadder
canonicalHighestAlphaClayLemmaLadderRound25 =
  highestAlphaClayLemmaLadder
    exactTarget
    checkedReducer
    checkedReducer
    physicalProducerOpen
    checkedExact
    checkedExact
    checkedExact
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    physicalProducerOpen
    checkedReducer
    checkedReducer
    physicalProducerOpen
    physicalProducerOpen
    checkedReducer
    physicalProducerOpen
    physicalProducerOpen
    checkedReducer

round25L3AggregateIsStillOpen :
  R24.L3_periodicDivergenceFreeGalerkinFourierCarrier
    canonicalHighestAlphaClayLemmaLadderRound25
  ≡ physicalProducerOpen
round25L3AggregateIsStillOpen = refl

round25L4PhysicalSupportIsCheckedExact :
  R24.L4_exhaustiveBonyAndCommutatorSupportPartition
    canonicalHighestAlphaClayLemmaLadderRound25
  ≡ checkedExact
round25L4PhysicalSupportIsCheckedExact = refl

record L3LiteralGalerkinSubstatus : Set where
  constructor l3-literal-galerkin-substatus
  field
    cutoffCubeAndTriadEnumeration : R24.LemmaState
    outputFibresSoundCompleteDuplicateFree : R24.LemmaState
    realityCarrierNegationClosure : R24.LemmaState
    exactLerayProjectedCoefficient : R24.LemmaState
    physicalFourierCoefficientEquivalence : R24.LemmaState
    finiteDimensionalODEExistence : R24.LemmaState
    realityTransversalityPropagation : R24.LemmaState

open L3LiteralGalerkinSubstatus public

canonicalL3LiteralGalerkinSubstatus : L3LiteralGalerkinSubstatus
canonicalL3LiteralGalerkinSubstatus =
  l3-literal-galerkin-substatus
    checkedExact
    checkedExact
    checkedExact
    checkedExact
    checkedExact
    physicalProducerOpen
    physicalProducerOpen

record L4PhysicalSupportSubstatus : Set where
  constructor l4-physical-support-substatus
  field
    totalActualTriadClassification : R24.LemmaState
    uniqueActualTriadClassification : R24.LemmaState
    lowLowFarOutputExclusion : R24.LemmaState
    lowHighOutputTracking : R24.LemmaState
    highLowOutputTracking : R24.LemmaState
    highHighInputComparability : R24.LemmaState
    outputFibreExactRecomposition : R24.LemmaState
    exactFiveSourceSum : R24.LemmaState
    unnamedRemainderAbsent : R24.LemmaState

open L4PhysicalSupportSubstatus public

canonicalL4PhysicalSupportSubstatus : L4PhysicalSupportSubstatus
canonicalL4PhysicalSupportSubstatus =
  l4-physical-support-substatus
    checkedExact checkedExact checkedExact
    checkedExact checkedExact checkedExact
    checkedExact checkedExact checkedExact

------------------------------------------------------------------------
-- Exact theorem evidence, not Boolean receipts.
------------------------------------------------------------------------

record Round25ExactEvidence : Set₁ where
  field
    literalCarrierCertificate :
      (cutoff : Nat) →
      Carrier.LiteralGalerkinCarrierCertificate cutoff

    lowLowCannotReachFarHigherOutput :
      (τ : Physical.PhysicalTriadIncidence) →
      Shell.shellIndex (Physical.p τ) + Shell.Csep
        ≤ Shell.shellIndex (Physical.k τ) →
      Shell.shellIndex (Physical.q τ) + Shell.Csep
        ≤ Shell.shellIndex (Physical.k τ) →
      ⊥

    actualFiveSourcePartition :
      (cutoff : Nat) →
      (output : Z3.FourierMode) →
      (value : Physical.PhysicalTriadIncidence → ℚ) →
      (commutatorValue : ℚ) →
      Sum.fiveSourceTotal cutoff output value commutatorValue
      ≡
      DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact.highHighToLowSum
        (Sum.physicalTaggedOutputFiber cutoff output value)
      + DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact.lowHighSum
        (Sum.physicalTaggedOutputFiber cutoff output value)
      + DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact.highLowSum
        (Sum.physicalTaggedOutputFiber cutoff output value)
      + DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact.comparableSum
        (Sum.physicalTaggedOutputFiber cutoff output value)
      + commutatorValue

open Round25ExactEvidence public

canonicalRound25ExactEvidence : Round25ExactEvidence
canonicalRound25ExactEvidence = record
  { literalCarrierCertificate =
      Carrier.literalGalerkinCarrierCertificate
  ; lowLowCannotReachFarHigherOutput =
      Support.noTwoInputsThreeShellsBelowOutput
  ; actualFiveSourcePartition =
      Sum.physicalFiveSourcePartitionExact
  }

record Round25HighestAlphaBoundary : Set where
  constructor round25-highest-alpha-boundary
  field
    literalFiniteCarrierCertified : Bool
    outputFibreDuplicateFreeProved : Bool
    physicalFiveClassSupportClosed : Bool
    physicalFiveSourceSumClosed : Bool
    L4PromotedToCheckedExact : Bool
    L3AggregateFullyClosed : Bool
    classwiseCutoffUniformAnalyticTaxesProduced : Bool
    strictTotalViscosityMarginProduced : Bool
    unconditionalClayTheoremPromoted : Bool

open Round25HighestAlphaBoundary public

canonicalRound25HighestAlphaBoundary : Round25HighestAlphaBoundary
canonicalRound25HighestAlphaBoundary =
  round25-highest-alpha-boundary
    true true true true true false false false false

l3AggregateRemainsOpen :
  L3AggregateFullyClosed canonicalRound25HighestAlphaBoundary ≡ false
l3AggregateRemainsOpen = refl

classwisePhysicalTaxesRemainOpen :
  classwiseCutoffUniformAnalyticTaxesProduced
    canonicalRound25HighestAlphaBoundary
  ≡ false
classwisePhysicalTaxesRemainOpen = refl

strictMarginRemainsOpen :
  strictTotalViscosityMarginProduced
    canonicalRound25HighestAlphaBoundary
  ≡ false
strictMarginRemainsOpen = refl

round25ClayPromotionRemainsFalse :
  unconditionalClayTheoremPromoted
    canonicalRound25HighestAlphaBoundary
  ≡ false
round25ClayPromotionRemainsFalse = refl
