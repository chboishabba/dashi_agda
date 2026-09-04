module DASHI.Reasoning.JusticeLeeSensibLawBidiSearchClosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as SL
import DASHI.Reasoning.JusticeLeeSensibLawAdversarialProofGraphBidiExact as Legal
import DASHI.Reasoning.JusticeLeeSensibLawExperimentSearchCrossPollinationExact as Cross

------------------------------------------------------------------------
-- BIDI SEARCH CLOSURE
--
-- This owner strengthens the Lee/SensibLaw construction from records that may
-- carry reverse-search obligations into an explicit consumer-indexed compiler:
--
--   procedural consumer
--   -> unresolved legal coordinate
--   -> required proof obligation
--   -> discriminator class
--   -> evidence probe class.
--
-- It remains a DASHI construction.  It does not claim that Justice Lee states
-- these mathematical functions or that a legal dispute has a unique objectively
-- minimal next probe without a declared consumer and policy.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Consumer-indexed unresolved coordinate.
------------------------------------------------------------------------

data ProceduralConsumer : Set where
  identifyCommonGround
  isolateLiveControversy
  prepareEvidenceConference
  prepareForAdjudication
  : ProceduralConsumer

data ResidualCoordinate : Set where
  nodeCoordinate
  relationCoordinate
  evidenceCoordinate
  characterisationCoordinate
  causationCoordinate
  legalConsequenceCoordinate
  : ResidualCoordinate

data ObligationKind : Set where
  establishOccurrence
  establishRelation
  establishReliability
  establishCharacterisation
  establishCausation
  establishLegalConsequence
  : ObligationKind

data DiscriminatorKind : Set where
  sourceDiscriminator
  relationDiscriminator
  reliabilityDiscriminator
  characterisationDiscriminator
  causationDiscriminator
  consequenceDiscriminator
  : DiscriminatorKind

residualCoordinate : Legal.DisagreementKind → ResidualCoordinate
residualCoordinate Legal.nodeDisagreement = nodeCoordinate
residualCoordinate Legal.relationDisagreement = relationCoordinate
residualCoordinate Legal.evidenceDisagreement = evidenceCoordinate
residualCoordinate Legal.characterisationDisagreement = characterisationCoordinate
residualCoordinate Legal.causationDisagreement = causationCoordinate
residualCoordinate Legal.legalConsequenceDisagreement = legalConsequenceCoordinate

obligationFor : ResidualCoordinate → ObligationKind
obligationFor nodeCoordinate = establishOccurrence
obligationFor relationCoordinate = establishRelation
obligationFor evidenceCoordinate = establishReliability
obligationFor characterisationCoordinate = establishCharacterisation
obligationFor causationCoordinate = establishCausation
obligationFor legalConsequenceCoordinate = establishLegalConsequence

discriminatorFor : ObligationKind → DiscriminatorKind
discriminatorFor establishOccurrence = sourceDiscriminator
discriminatorFor establishRelation = relationDiscriminator
discriminatorFor establishReliability = reliabilityDiscriminator
discriminatorFor establishCharacterisation = characterisationDiscriminator
discriminatorFor establishCausation = causationDiscriminator
discriminatorFor establishLegalConsequence = consequenceDiscriminator

probeFor : DiscriminatorKind → Cross.EvidenceProbe
probeFor sourceDiscriminator = Cross.inspectSourceSpan
probeFor relationDiscriminator = Cross.inspectCausalEdge
probeFor reliabilityDiscriminator = Cross.inspectReport
probeFor characterisationDiscriminator = Cross.inspectCharacterisation
probeFor causationDiscriminator = Cross.inspectCausalEdge
probeFor consequenceDiscriminator = Cross.inspectWitness

------------------------------------------------------------------------
-- 2. Literal reverse compiler.
------------------------------------------------------------------------

record CompiledSearchObligation : Set where
  constructor compiledSearchObligation
  field
    consumer : ProceduralConsumer
    residualKind : Legal.DisagreementKind
    coordinate : ResidualCoordinate
    obligation : ObligationKind
    discriminator : DiscriminatorKind
    probe : Cross.EvidenceProbe
    compilationReference : String

open CompiledSearchObligation public

compileSearchObligation :
  ProceduralConsumer →
  Legal.DisagreementKind →
  CompiledSearchObligation
compileSearchObligation consumer residual =
  compiledSearchObligation
    consumer
    residual
    (residualCoordinate residual)
    (obligationFor (residualCoordinate residual))
    (discriminatorFor (obligationFor (residualCoordinate residual)))
    (probeFor (discriminatorFor (obligationFor (residualCoordinate residual))))
    "consumer-indexed reverse compile from typed legal residual to proof obligation, discriminator class and evidence-probe class"

compiledProbeIsDeterminedByTypedResidual :
  ∀ consumer residual →
  CompiledSearchObligation.probe (compileSearchObligation consumer residual)
  ≡ probeFor (discriminatorFor (obligationFor (residualCoordinate residual)))
compiledProbeIsDeterminedByTypedResidual consumer residual = refl

------------------------------------------------------------------------
-- 3. Minimality is policy-relative, not absolute.
------------------------------------------------------------------------

data ProbeCost : Set where
  lowCost mediumCost highCost : ProbeCost

record ProbePolicy : Set where
  constructor probePolicy
  field
    cost : Cross.EvidenceProbe → ProbeCost
    admissible : Cross.EvidenceProbe → Bool
    policyReference : String

open ProbePolicy public

record PolicyAdmittedCompiledProbe
    (policy : ProbePolicy)
    (compiled : CompiledSearchObligation) : Set where
  constructor policyAdmittedCompiledProbe
  field
    admitted : ProbePolicy.admissible policy (CompiledSearchObligation.probe compiled) ≡ true
    admissionReference : String

open PolicyAdmittedCompiledProbe public

record MinimalityBoundary : Set where
  constructor minimalityBoundary
  field
    typedResidualAloneDeterminesGloballyOptimalEvidenceProbe : Bool
    typedResidualAloneDeterminesGloballyOptimalEvidenceProbeIsFalse :
      typedResidualAloneDeterminesGloballyOptimalEvidenceProbe ≡ false

    declaredConsumerAndProbePolicyAreRequiredForMinimalityClaim : Bool
    declaredConsumerAndProbePolicyAreRequiredForMinimalityClaimIsTrue :
      declaredConsumerAndProbePolicyAreRequiredForMinimalityClaim ≡ true

canonicalMinimalityBoundary : MinimalityBoundary
canonicalMinimalityBoundary =
  minimalityBoundary
    false refl
    true refl

------------------------------------------------------------------------
-- 4. Search is indexed by live controversy, not the whole corpus.
------------------------------------------------------------------------

record ResidualIndexedSearchBoundary : Set where
  constructor residualIndexedSearchBoundary
  field
    searchWholeCorpusWithoutLiveObligationIsRequired : Bool
    searchWholeCorpusWithoutLiveObligationIsRequiredIsFalse :
      searchWholeCorpusWithoutLiveObligationIsRequired ≡ false

    aResolvedCoordinateMayRemainOutsideNextProbe : Bool
    aResolvedCoordinateMayRemainOutsideNextProbeIsTrue :
      aResolvedCoordinateMayRemainOutsideNextProbe ≡ true

    sourceSimilarityAloneDischargesCompiledObligation : Bool
    sourceSimilarityAloneDischargesCompiledObligationIsFalse :
      sourceSimilarityAloneDischargesCompiledObligation ≡ false

canonicalResidualIndexedSearchBoundary : ResidualIndexedSearchBoundary
canonicalResidualIndexedSearchBoundary =
  residualIndexedSearchBoundary
    false refl
    true refl
    false refl

------------------------------------------------------------------------
-- 5. SensibLaw runtime bridge contract.
------------------------------------------------------------------------

record RuntimePNFBridge : Set₁ where
  constructor runtimePNFBridge
  field
    sourceText : Set
    sourceDocument : Set
    emit : sourceText → List SL.PNFEmissionReceipt
    documentOf : sourceText → sourceDocument
    emittedReceiptRetainsSourceSpan : Bool
    emittedReceiptRetainsSourceSpanIsTrue :
      emittedReceiptRetainsSourceSpan ≡ true
    graphAdmissionMayInventUnreceiptedPredicate : Bool
    graphAdmissionMayInventUnreceiptedPredicateIsFalse :
      graphAdmissionMayInventUnreceiptedPredicate ≡ false
    bridgeReference : String

open RuntimePNFBridge public

------------------------------------------------------------------------
-- 6. Capstone closure status.
------------------------------------------------------------------------

record LeeSensibLawBidiClosure : Set₂ where
  constructor leeSensibLawBidiClosure
  field
    residualCompilerOwned : Bool
    residualCompilerOwnedIsTrue : residualCompilerOwned ≡ true
    policyRelativeMinimalityOwned : Bool
    policyRelativeMinimalityOwnedIsTrue : policyRelativeMinimalityOwned ≡ true
    runtimeBridgeContractOwned : Bool
    runtimeBridgeContractOwnedIsTrue : runtimeBridgeContractOwned ≡ true
    actualRuntimeEmissionReceiptAcquired : Bool
    actualRuntimeEmissionReceiptAcquiredIsFalse :
      actualRuntimeEmissionReceiptAcquired ≡ false
    empiricalLeeExperimentCompleted : Bool
    empiricalLeeExperimentCompletedIsFalse :
      empiricalLeeExperimentCompleted ≡ false
    closureReference : String

canonicalLeeSensibLawBidiClosure : LeeSensibLawBidiClosure
canonicalLeeSensibLawBidiClosure =
  leeSensibLawBidiClosure
    true refl
    true refl
    true refl
    false refl
    false refl
    "formal reverse residual->obligation->discriminator->probe compiler is owned; true optimality remains consumer/policy-relative; the runtime PNF contract is specified, but no actual runtime emission or controlled Lee experiment is claimed yet"
