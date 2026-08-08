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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

------------------------------------------------------------------------
-- Concrete theorem anchors preventing status-only promotion.
------------------------------------------------------------------------

literalCarrierCertificateAnchor :
  (cutoff : Agda.Builtin.Nat.Nat) →
  Carrier.LiteralGalerkinCarrierCertificate cutoff
literalCarrierCertificateAnchor =
  Carrier.literalGalerkinCarrierCertificate
  where
  import Agda.Builtin.Nat

lowLowFarOutputNoGoAnchor =
  Support.noTwoInputsThreeShellsBelowOutput

physicalFiveSourceSumAnchor =
  Sum.physicalFiveSourcePartitionExact
