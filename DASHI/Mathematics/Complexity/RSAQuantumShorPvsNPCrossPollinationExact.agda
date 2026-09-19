module DASHI.Mathematics.Complexity.RSAQuantumShorPvsNPCrossPollinationExact where

------------------------------------------------------------------------
-- RSA / SHOR / P-VERSUS-NP CROSS-POLLINATION
--
-- This module does not identify BQP with P and does not promote factoring to
-- an NP-complete problem.  It compiles existing repository facts into one
-- complexity-theory boundary:
--
--   same mathematical consumer
--     /= same computational model
--     /= same execution path
--     /= same cost coordinate.
--
-- Positive content is reused from the existing Shor/RSA/fibre machinery.
-- WrongType promotions remain uninhabited.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Core.EfficientRecoverableQuotientExact as ERQ
import DASHI.Crypto.ShorFactoring as Shor
import DASHI.ComputerScience.ShorOrderClassicalQuantumMachineComparisonExact as Comparison
import DASHI.ComputerScience.FactorProducerReceiptExact as Producer
import DASHI.ComputerScience.RSA260ShorColouring369MonsterSymmetrySearchExact as Symmetry
import DASHI.Reasoning.TypedHyperfabricConsumerReductionBridgeExact as HyperReduction
import DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact as PantsGluing

------------------------------------------------------------------------
-- Execution fibres are different coordinates even when they feed the same
-- arithmetic consumer.
------------------------------------------------------------------------

data ExecutionFibre : Set where
  deterministicClassical : ExecutionFibre
  nondeterministicCertificate : ExecutionFibre
  quantumShor : ExecutionFibre

classicalIsNotQuantum :
  deterministicClassical ≡ quantumShor → ⊥
classicalIsNotQuantum ()

certificateIsNotQuantum :
  nondeterministicCertificate ≡ quantumShor → ⊥
certificateIsNotQuantum ()

classicalIsNotCertificate :
  deterministicClassical ≡ nondeterministicCertificate → ⊥
classicalIsNotCertificate ()

------------------------------------------------------------------------
-- Existing factor receipts give the strongest finite same-consumer witness:
-- identical certified factor evidence can be carried by different producers.
------------------------------------------------------------------------

factor15EvidenceSameAcrossClassicalAndQuantumReceipts :
  Producer.evidence Producer.factor15ClassicalReceipt
  ≡ Producer.evidence Producer.factor15QuantumReceipt
factor15EvidenceSameAcrossClassicalAndQuantumReceipts = refl

factor21EvidenceSameAcrossClassicalAndQuantumReceipts :
  Producer.evidence Producer.factor21ClassicalReceipt
  ≡ Producer.evidence Producer.factor21QuantumReceipt
factor21EvidenceSameAcrossClassicalAndQuantumReceipts = refl

factor15ClassicalProducerIsClassical :
  Producer.producerClass Producer.factor15ClassicalReceipt
  ≡ Producer.classicalOrderFindingProducer
factor15ClassicalProducerIsClassical = refl

factor15QuantumProducerIsQuantum :
  Producer.producerClass Producer.factor15QuantumReceipt
  ≡ Producer.quantumShorProducer
factor15QuantumProducerIsQuantum = refl

factor15ProducerClassesRemainDistinct :
  Producer.producerClass Producer.factor15ClassicalReceipt
  ≡ Producer.producerClass Producer.factor15QuantumReceipt →
  ⊥
factor15ProducerClassesRemainDistinct ()

------------------------------------------------------------------------
-- The existing classical/quantum order comparison pays equality only at the
-- consumer.  It explicitly does not identify path or cost coordinates.
------------------------------------------------------------------------

sameOrderConsumerAlreadyPaid :
  Comparison.commonOrderConsumerExact
    Comparison.canonicalShorOrderCrossParadigmBoundary
  ≡ true
sameOrderConsumerAlreadyPaid = refl

sameOrderDoesNotIdentifyExecutionPath :
  Comparison.sameOrderImpliesSameExecutionPath
    Comparison.canonicalShorOrderCrossParadigmBoundary
  ≡ false
sameOrderDoesNotIdentifyExecutionPath = refl

classicalTransitionsDoNotBecomeQuantumGateCounts :
  Comparison.classicalTransitionCountEqualsQuantumGateCount
    Comparison.canonicalShorOrderCrossParadigmBoundary
  ≡ false
classicalTransitionsDoNotBecomeQuantumGateCounts = refl

------------------------------------------------------------------------
-- Shor supplies a real symmetry/quotient/transform template.  RSA-260 itself
-- still has no certified quantum run or certified quantum resource estimate.
------------------------------------------------------------------------

shorHiddenPeriodSurfaceExists :
  Symmetry.modularOrderPresentedAsHiddenPeriod
    Symmetry.canonicalShorSymmetryBoundary
  ≡ true
shorHiddenPeriodSurfaceExists = refl

shorFourierPeriodMachineExists :
  Symmetry.FourierTransformPresentInPeriodMachine
    Symmetry.canonicalShorSymmetryBoundary
  ≡ true
shorFourierPeriodMachineExists = refl

shorRecoveredPeriodFeedsCertifiedSplit :
  Symmetry.exactRecoveredPeriodCanFeedCertifiedClassicalSplit
    Symmetry.canonicalShorSymmetryBoundary
  ≡ true
shorRecoveredPeriodFeedsCertifiedSplit = refl

rsa260QuantumRunStillOpen :
  Symmetry.rsa260QuantumOrderFindingRunConstructed
    Symmetry.canonicalShorSymmetryBoundary
  ≡ false
rsa260QuantumRunStillOpen = refl

rsa260QuantumResourceEstimateStillOpen :
  Symmetry.rsa260QuantumResourceEstimateCertified
    Symmetry.canonicalShorSymmetryBoundary
  ≡ false
rsa260QuantumResourceEstimateStillOpen = refl

------------------------------------------------------------------------
-- Later generic machinery is relevant because it expresses the exact shape
-- required by a structural reduction: selected compatible sections may be
-- reduced for a declared consumer, and seams require explicit interface
-- compatibility.  Neither theorem manufactures an efficient NP witness
-- producer by itself.
------------------------------------------------------------------------

hyperfabricSelectedSectionReductionAvailable :
  HyperReduction.reductionActsOnSelectedCompatibleSectionCodes
    HyperReduction.canonicalHyperfabricConsumerReductionBoundary
  ≡ true
hyperfabricSelectedSectionReductionAvailable = refl

hyperfabricReductionDoesNotCollapsePhysicalFabric :
  HyperReduction.consumerReductionCollapsesPhysicalHyperfabric
    HyperReduction.canonicalHyperfabricConsumerReductionBoundary
  ≡ false
hyperfabricReductionDoesNotCollapsePhysicalFabric = refl

pantsSeamRequiresAndCarriesInterfaceMatch :
  PantsGluing.interfaceMatchAuthorizesTypedSeam
    PantsGluing.canonicalTypedHyperfabricPantsGluingBoundary
  ≡ true
pantsSeamRequiresAndCarriesInterfaceMatch = refl

------------------------------------------------------------------------
-- The classical theorem remains exactly the standard one: an NP-complete
-- language in deterministic classical P yields P=NP.  A quantum factoring
-- producer is not an inhabitant of the required InP target.
------------------------------------------------------------------------

npCompleteInClassicalPStillCompilesPEqualsNP :
  ∀ {Word} {cost : PR.PolynomialCostModel Word}
    (pSubsetNP : PR.PIncludedInNP cost)
    (target : PR.Language Word) →
  PR.NPComplete cost target →
  PR.InP cost target →
  PR.PEqualsNP cost
npCompleteInClassicalPStillCompilesPEqualsNP =
  PR.npCompleteInPImpliesPEqualsNP

verifierAloneStillDoesNotConstructWitness :
  ERQ.WitnessConstructionFromVerifier ERQ.verificationOnly → ⊥
verifierAloneStillDoesNotConstructWitness =
  ERQ.verifierDoesNotConstructWitness

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data QuantumFactoringAuthorizesClassicalPPromotion : Set where
data FactoringAuthorizesNPCompletenessPromotion : Set where
data SymmetryTemplateAuthorizesUniformNPRecovery : Set where
data EfficientQuotientShapeAuthorizesPEqualsNP : Set where

quantumFactoringDoesNotAuthorizeClassicalP :
  QuantumFactoringAuthorizesClassicalPPromotion → ⊥
quantumFactoringDoesNotAuthorizeClassicalP ()

factoringDoesNotAuthorizeNPCompleteness :
  FactoringAuthorizesNPCompletenessPromotion → ⊥
factoringDoesNotAuthorizeNPCompleteness ()

shorSymmetryTemplateDoesNotAuthorizeUniformNPRecovery :
  SymmetryTemplateAuthorizesUniformNPRecovery → ⊥
shorSymmetryTemplateDoesNotAuthorizeUniformNPRecovery ()

efficientQuotientShapeDoesNotAuthorizePEqualsNP :
  EfficientQuotientShapeAuthorizesPEqualsNP → ⊥
efficientQuotientShapeDoesNotAuthorizePEqualsNP ()

------------------------------------------------------------------------
-- Updated frontier.  The old Cook--Levin residual remains a formalisation
-- obligation, but the research frontier is more accurately split into:
--   * generic Cook--Levin/CNF polynomiality;
--   * uniform deterministic-classical recovery for NP-complete witnesses;
--   * or a genuine classical super-polynomial obstruction.
------------------------------------------------------------------------

record PvsNPRSAQuantumCrossPollinationBoundary : Set where
  constructor pvsnp-rsa-quantum-crosspollination-boundary
  field
    standardPAndNPCarriersPresent : Bool
    producerVerifierSeparationPresent : Bool
    computationalModelFibreSeparationPresent : Bool
    shorSymmetryReductionTemplatePresent : Bool
    recoverableQuotientInfrastructurePresent : Bool
    hyperfabricConsumerReductionInfrastructurePresent : Bool
    explicitSeamCompatibilityInfrastructurePresent : Bool

    genericCookLevinCNFPolynomialityPaid : Bool
    uniformClassicalRecoveryForNPCompleteWitnessesPaid : Bool
    classicalSuperPolynomialLowerBoundPaid : Bool
    classicalPvsNPResolved : Bool

open PvsNPRSAQuantumCrossPollinationBoundary public

canonicalPvsNPRSAQuantumCrossPollinationBoundary :
  PvsNPRSAQuantumCrossPollinationBoundary
canonicalPvsNPRSAQuantumCrossPollinationBoundary =
  pvsnp-rsa-quantum-crosspollination-boundary
    true true true true true true true
    false false false false

classicalPvsNPStillOpen :
  classicalPvsNPResolved canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ false
classicalPvsNPStillOpen = refl

genericCookLevinStillOpen :
  genericCookLevinCNFPolynomialityPaid
    canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ false
genericCookLevinStillOpen = refl

uniformClassicalRecoveryStillOpen :
  uniformClassicalRecoveryForNPCompleteWitnessesPaid
    canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ false
uniformClassicalRecoveryStillOpen = refl

classicalLowerBoundStillOpen :
  classicalSuperPolynomialLowerBoundPaid
    canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ false
classicalLowerBoundStillOpen = refl
