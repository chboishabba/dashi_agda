module DASHI.Cognition.CCDCOEP3ClimateGenealogyCaseExact where

------------------------------------------------------------------------
-- CCDCOE P3: ONE BOUNDED, SOURCE-OWNED CLIMATE-DOUBT CASE.
--
-- Original EvidenceGradedGenealogyCasesExact owns the Oreskes/Conway
-- tobacco-to-climate grade-B continuity edge. Here the actual source edge
-- is retained; it is not recast as a record of central command.
--
-- The additional command/intent alternatives below are finite candidate
-- causal worlds, not assertions about real institutions or individuals.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy
import DASHI.Governance.EvidenceGradedGenealogyCasesExact as Cases
import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.IntersectionalNonFactorability as NF

-- A historical relation with original source identifiers and qualification.
originalClimateContinuity : Genealogy.EvidenceEdge
originalClimateContinuity = Cases.tobaccoToClimateHistoricalContinuity

originalHistoricalRelation :
  Genealogy.relation originalClimateContinuity
  ≡ Genealogy.personnelInstitutionalContinuity
originalHistoricalRelation = refl

originalEvidenceGrade :
  Genealogy.grade originalClimateContinuity ≡ Genealogy.gradeB
originalEvidenceGrade = refl

originalSourceList :
  Genealogy.sources originalClimateContinuity
  ≡ (Sources.merchantsOfDoubtHistory ∷
     Sources.oreskesConwayNatureCommentary ∷ [])
originalSourceList = refl

historicalContinuityHasStrongReceipt :
  Genealogy.StrongEvidenceEdge originalClimateContinuity
historicalContinuityHasStrongReceipt = Cases.tobaccoToClimateIsStrong

-- The real source grade remains different from mere co-circulation.
adjacencyGrade :
  Genealogy.grade Cases.wellnessToAntiVaxAdjacency
  ≡ Genealogy.gradeC
adjacencyGrade = refl

adjacencyDoesNotProvideStrongTransfer :
  Genealogy.StrongEvidenceEdge Cases.wellnessToAntiVaxAdjacency → ⊥
adjacencyDoesNotProvideStrongTransfer =
  Cases.wellnessAdjacencyIsNotStrongHistoricalTransfer

-- These are distinct evidence objects, not two interpretations of one
-- observation. The bundle selects the claimed historical relation's grade.
data ComparedSource : Set where
  documentedContinuity boundedAdjacency : ComparedSource

evidenceGrade : ComparedSource → Genealogy.EvidenceGrade
evidenceGrade documentedContinuity =
  Genealogy.grade originalClimateContinuity
evidenceGrade boundedAdjacency =
  Genealogy.grade Cases.wellnessToAntiVaxAdjacency

data GenericInfluenceLabel : Set where
  broadInfluenceLabel : GenericInfluenceLabel

genericSurface : ComparedSource → GenericInfluenceLabel
genericSurface _ = broadInfluenceLabel

differentHistoricalGrades :
  evidenceGrade documentedContinuity
  ≡ evidenceGrade boundedAdjacency → ⊥
differentHistoricalGrades ()

originalEvidenceGradeBundle :
  Discriminator.ExperimentBundle ComparedSource
originalEvidenceGradeBundle =
  Discriminator.experimentBundle
    Genealogy.EvidenceGrade
    evidenceGrade
    1
    "Read the source-owned evidence grade instead of a broad pipeline label"
    "Existing bounded genealogy receipts; not an effect-size estimate"

originalEvidenceGradeSeparates :
  Discriminator.BundleSeparates originalEvidenceGradeBundle
    documentedContinuity boundedAdjacency
originalEvidenceGradeSeparates =
  Discriminator.bundleSeparates differentHistoricalGrades

sourceGradeLanguageExtension :
  Discriminator.DiscriminatingLanguageExtension genericSurface
sourceGradeLanguageExtension =
  Discriminator.discriminatingLanguageExtension
    (Discriminator.currentObserverCollision
      documentedContinuity boundedAdjacency refl)
    originalEvidenceGradeBundle
    originalEvidenceGradeSeparates

sourceGradeCannotFactorThroughGenericLabel :
  NF.FactorsThrough genericSurface evidenceGrade → ⊥
sourceGradeCannotFactorThroughGenericLabel =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      documentedContinuity boundedAdjacency refl
      differentHistoricalGrades)

------------------------------------------------------------------------
-- Actual tobacco-climate continuity is compatible with more than one
-- command/coordination hypothesis. We DO NOT encode a command receipt.
------------------------------------------------------------------------

data CoordinationHypothesis : Set where
  sharedStrategyWithoutSingleCommand : CoordinationHypothesis
  centrallyCommandedStrategy : CoordinationHypothesis
  unresolvedMixedStrategy : CoordinationHypothesis

-- Explicit candidate worlds, not three observed historical cases.
record ClimateCausalCandidate : Set where
  constructor climateCausalCandidate
  field
    historicalEdge : Genealogy.EvidenceEdge
    commandHypothesis : CoordinationHypothesis

open ClimateCausalCandidate public

decentralisedCandidate : ClimateCausalCandidate
decentralisedCandidate =
  climateCausalCandidate originalClimateContinuity
    sharedStrategyWithoutSingleCommand

centralisedCandidate : ClimateCausalCandidate
centralisedCandidate =
  climateCausalCandidate originalClimateContinuity
    centrallyCommandedStrategy

mixedCandidate : ClimateCausalCandidate
mixedCandidate =
  climateCausalCandidate originalClimateContinuity
    unresolvedMixedStrategy

-- Same actual grade-B historical evidence for all candidate mechanisms.
publicHistoricalGrade :
  ClimateCausalCandidate → Genealogy.EvidenceGrade
publicHistoricalGrade candidate =
  Genealogy.grade (historicalEdge candidate)

samePublishedHistoricalGrade :
  publicHistoricalGrade decentralisedCandidate
  ≡ publicHistoricalGrade centralisedCandidate
samePublishedHistoricalGrade = refl

centralCommandAndContinuityAreDifferent :
  commandHypothesis decentralisedCandidate
  ≡ commandHypothesis centralisedCandidate → ⊥
centralCommandAndContinuityAreDifferent ()

gradeBDoesNotIdentifyCentralCommand :
  NF.FactorsThrough publicHistoricalGrade commandHypothesis → ⊥
gradeBDoesNotIdentifyCentralCommand =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      decentralisedCandidate centralisedCandidate
      samePublishedHistoricalGrade
      centralCommandAndContinuityAreDifferent)

-- This is a MODEL discriminator: it asks for additional directly
-- documented command evidence rather than pretending that it exists.
data CommandEvidence : Set where
  commandDocumented commandNotDocumented commandUnresolved : CommandEvidence

hypotheticalCommandObservation :
  ClimateCausalCandidate → CommandEvidence
hypotheticalCommandObservation candidate with commandHypothesis candidate
... | sharedStrategyWithoutSingleCommand = commandNotDocumented
... | centrallyCommandedStrategy = commandDocumented
... | unresolvedMixedStrategy = commandUnresolved

candidateCommandProbe :
  Discriminator.ExperimentBundle ClimateCausalCandidate
candidateCommandProbe =
  Discriminator.experimentBundle
    CommandEvidence
    hypotheticalCommandObservation
    1
    "Seek independently attributable command and responsibility documents"
    "Hypothetical oracle only; no actual command archival receipt admitted"

centralisationHypothesesCanBeSeparatedIfEvidenceExists :
  Discriminator.BundleSeparates candidateCommandProbe
    decentralisedCandidate centralisedCandidate
centralisationHypothesesCanBeSeparatedIfEvidenceExists =
  Discriminator.bundleSeparates (λ ())

commandProbeLanguageExtension :
  Discriminator.DiscriminatingLanguageExtension publicHistoricalGrade
commandProbeLanguageExtension =
  Discriminator.discriminatingLanguageExtension
    (Discriminator.currentObserverCollision
      decentralisedCandidate centralisedCandidate
      samePublishedHistoricalGrade)
    candidateCommandProbe
    centralisationHypothesesCanBeSeparatedIfEvidenceExists

-- Every assertion above remains either an actual bounded source relation,
-- or a labelled counterfactual/candidate-world construct. A real-case claim
-- about effects on public beliefs, policy, or coordinated responsibility
-- still needs original intervention/exposure and outcome observations.
