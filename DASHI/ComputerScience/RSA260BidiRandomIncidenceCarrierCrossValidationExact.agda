module DASHI.ComputerScience.RSA260BidiRandomIncidenceCarrierCrossValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact as Sources
import DASHI.ComputerScience.RSA260BidiCarrierPreparationCrossValidationExact as Prior

------------------------------------------------------------------------
-- RANDOM-FINE-INCIDENCE BIDI CARRIER CROSS-VALIDATION
--
-- The prior carrier/preparation experiment varied only cyclic-interval row
-- geometry.  This owner replaces that fine incidence by independently sampled
-- exact-degree rows while retaining the coarse executable shadow contract:
--
--   924 x 512 over GF(2)
--   six rows of degree 151, 918 rows of degree 150
--   rank 512 / left-nullity 412.
--
-- Result: no tested randomized carrier/preparation pair admitted a withheld-
-- valid shared generator at d <= 40, but every pair admitted one after the
-- search was escalated to d <= 80.  The first fitting degrees were 65 or 66,
-- and the resulting shifted Krylov relations still recovered nonzero kernels.
--
-- Therefore the coarse contract does not determine low-degree recurrence
-- geometry.  Failure at d <= 40 is a bounded-ansatz counterexample, not a
-- proof that the consumer is impossible.
------------------------------------------------------------------------

priorCarrierPreparationBoundary : Prior.CarrierPreparationCrossBoundary
priorCarrierPreparationBoundary = Prior.canonicalCarrierPreparationCrossBoundary

------------------------------------------------------------------------
-- Snowball attribution: identity/provenance coordinates, not proof.
------------------------------------------------------------------------

luRSA260ExecutionPrimary : Source.AttributedSource
luRSA260ExecutionPrimary =
  Source.mkNoDOISource
    "Eric Lu"
    "Factoring RSA-260"
    "Cognition"
    "2026"
    "https://cognition.com/blog/factoring-rsa-260"
    Source.practitionerSource
    "primary first-party execution source for the RSA-260 matrix and Block-Wiedemann-stage run envelope"
    Source.publicAttribution

wiedemannSparseFiniteFieldPrimary : Source.AttributedSource
wiedemannSparseFiniteFieldPrimary =
  Source.mkDOISource
    "Douglas H. Wiedemann"
    "Solving sparse linear equations over finite fields"
    "IEEE Transactions on Information Theory 32(1)"
    "1986"
    "10.1109/TIT.1986.1057137"
    "https://doi.org/10.1109/TIT.1986.1057137"
    Source.academicArticleSource
    "primary upstream algorithm source for sparse linear solving over finite fields"
    Source.publicAttribution

coppersmithBlockWiedemannPrimary : Source.AttributedSource
coppersmithBlockWiedemannPrimary = Sources.coppersmithBlockWiedemannPrimary

randomIncidenceSourceAtlas : Source.AttributedSourceAtlas
randomIncidenceSourceAtlas =
  Source.mkSourceAtlas
    "RSA-260 bidi random-incidence carrier experiment sources"
    "DASHI.ComputerScience.RSA260BidiRandomIncidenceCarrierCrossValidationExact"
    (luRSA260ExecutionPrimary ∷ coppersmithBlockWiedemannPrimary ∷ wiedemannSparseFiniteFieldPrimary ∷ [])
    "Lu pays RSA-260 execution coordinates; Coppersmith and Wiedemann pay algorithm lineage.  None identify the synthetic randomized carrier or import experimental conclusions."

record SnowballIdentityCoordinates : Set where
  constructor snowball-identity-coordinates
  field
    generalNumberFieldSieveQID : Sources.IdentifierApplicability
    sparseMatrixQID : Sources.IdentifierApplicability
    finiteFieldQID : Sources.IdentifierApplicability
    rsaCryptosystemQID : Sources.IdentifierApplicability
    blockWiedemannQID : Sources.IdentifierApplicability
    deweyCoordinate : Sources.IdentifierApplicability
    oeisCoordinate : Sources.IdentifierApplicability
open SnowballIdentityCoordinates public

currentSnowballIdentityCoordinates : SnowballIdentityCoordinates
currentSnowballIdentityCoordinates = snowball-identity-coordinates
  (Sources.identifierRecorded "Q140770")
  (Sources.identifierRecorded "Q1050404")
  (Sources.identifierRecorded "Q603880")
  (Sources.identifierRecorded "Q181551")
  Sources.identifierUnresolved
  Sources.identifierUnresolved
  Sources.identifierNotApplicable

------------------------------------------------------------------------
-- Exact executable provenance.
------------------------------------------------------------------------

record RandomIncidenceRuntimeSource : Set where
  constructor random-incidence-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    dependencyPath : String
    dependencyGitBlob : String
    exactTopLevelBlobExecuted : Bool
    exactDependencyBlobExecuted : Bool
open RandomIncidenceRuntimeSource public

currentRandomIncidenceRuntimeSource : RandomIncidenceRuntimeSource
currentRandomIncidenceRuntimeSource = random-incidence-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_random_incidence_crossvalidation.py"
  "760e21f9c86afcd27c089f1c27ed00b5a0a32dd7"
  "ddb26563d6da14d63e3b6f4daab1bc40363ed7c0"
  "rsa260_bidi_candidate_robustness.py"
  "0f60c28f01b50c2337f2e5dec0016f918119371d"
  true
  true

------------------------------------------------------------------------
-- Experimental receipt.
------------------------------------------------------------------------

record RandomIncidenceCrossValidationReceipt : Set where
  constructor random-incidence-cross-validation-receipt
  field
    carrierRows : Nat
    carrierColumns : Nat
    rowExcess : Nat
    randomizedCarriersTested : Nat
    degree151RowsPerCarrier : Nat
    degree150RowsPerCarrier : Nat
    allRandomizedCarriersFullRank : Bool
    allRandomizedCarriersLeftNullity412 : Bool
    preparationsPerCarrier : Nat
    lowDegreeSearchBound : Nat
    lowDegreeRuns : Nat
    lowDegreeRunsAdmitted : Nat
    escalatedSearchBound : Nat
    escalatedRuns : Nat
    escalatedRunsAdmitted : Nat
    minimumEscalatedGeneratorDegree : Nat
    maximumEscalatedGeneratorDegree : Nat
    allEscalatedShiftedRanks512 : Bool
    minimumObservedKernelWeight : Nat
    maximumObservedMinimumKernelWeight : Nat
    zeroShiftRelationsObserved : Nat
    consumerRecoveredDespiteZeroShift : Bool
    historicalProductionMatrixUsed : Bool
open RandomIncidenceCrossValidationReceipt public

currentRandomIncidenceCrossValidationReceipt : RandomIncidenceCrossValidationReceipt
currentRandomIncidenceCrossValidationReceipt = random-incidence-cross-validation-receipt
  924 512 412
  4
  6 918
  true true
  2
  40 8 0
  80 8 8
  65 66
  true
  425 449
  1
  true
  false

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record RandomIncidenceInterpretationBoundary : Set where
  constructor random-incidence-interpretation-boundary
  field
    coarseShapeDensityRankNullityDetermineLowDegreeGenerator : Bool
    cyclicIntervalLowDegreeBehaviourSurvivesRandomFineIncidence : Bool
    noGeneratorAtBound40ImpliesNoGenerator : Bool
    escalatingSearchRecoveredEveryTestedConsumer : Bool
    fineIncidenceMateriallyAffectsRecurrenceComplexity : Bool
    consumerSuccessIdentifiesHistoricalMatrix : Bool
    DOIImportsProof : Bool
    QIDImportsAuthority : Bool
    unresolvedDeweyMayBeInvented : Bool
open RandomIncidenceInterpretationBoundary public

canonicalRandomIncidenceInterpretationBoundary : RandomIncidenceInterpretationBoundary
canonicalRandomIncidenceInterpretationBoundary = random-incidence-interpretation-boundary
  false
  false
  false
  true
  true
  false
  false
  false
  false

------------------------------------------------------------------------
-- Next bidi residual.
------------------------------------------------------------------------

data RandomIncidenceResidual : Set where
  testMoreIndependentRandomCarriers : RandomIncidenceResidual
  measureRecurrenceDegreeDistribution : RandomIncidenceResidual
  deriveFineIncidencePredictorsOfGeneratorDegree : RandomIncidenceResidual
  compareAgainstSameObjectProductionArtifact : RandomIncidenceResidual

firstRandomIncidenceResidual : RandomIncidenceResidual
firstRandomIncidenceResidual = deriveFineIncidencePredictorsOfGeneratorDegree

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SameCoarseContractImpliesSameGeneratorGeometry : Set where
data BoundedSearchFailureImpliesConsumerFailure : Set where
data RandomCarrierConsumerSuccessImpliesHistoricalIdentity : Set where

sameCoarseContractDoesNotCreateGeneratorGeometry : SameCoarseContractImpliesSameGeneratorGeometry → ⊥
sameCoarseContractDoesNotCreateGeneratorGeometry ()

boundedSearchFailureDoesNotCreateConsumerFailure : BoundedSearchFailureImpliesConsumerFailure → ⊥
boundedSearchFailureDoesNotCreateConsumerFailure ()

randomCarrierConsumerDoesNotCreateHistoricalIdentity : RandomCarrierConsumerSuccessImpliesHistoricalIdentity → ⊥
randomCarrierConsumerDoesNotCreateHistoricalIdentity ()
