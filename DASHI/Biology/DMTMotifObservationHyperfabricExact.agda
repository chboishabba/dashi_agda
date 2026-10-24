module DASHI.Biology.DMTMotifObservationHyperfabricExact where

-- DMT/Erowid/Sanders/PNAS observation hyperfabric.
-- Thin instance of EXISTING typed hyperfabric and EvidenceHyperfabric owners;
-- no new universal sheaf, proof search or latent causal model.
--
-- Original publication: Noah, Shen, Earth Erowid, Fire Erowid, Silver
-- (2024), DOI 10.3389/fpsyg.2024.1397064.
-- Published category proportions are NOT temporal motifs or brain mechanisms.
--
-- Original method donor: Duta, Cassara, Silvestri, Lio, Sheaf Hypergraph
-- Networks (2023), arXiv:2309.17116. Our tiny finite incidence system
-- does not imply the paper's network learning or empirical performance.

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.EvidenceHyperfabricExact as Evidence
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Reasoning.TypedHyperfabricCore as Fabric
import DASHI.Biology.VisualMotifTransitionOperator as Motif
import DASHI.Biology.TernaryMotifNeuralObservationQuotientExact as NeuralQuotient

------------------------------------------------------------------------
-- Sites/fibres and admissible shared-observation hyperedges.
--
-- Incidence licenses WHICH source contributes to WHICH research consumer,
-- not a claim that any missing content or permission has been acquired.
------------------------------------------------------------------------

data ObservationFibre : Set where
  publishedErowidCategory : ObservationFibre
  sequencedErowidReport : ObservationFibre
  ErowidUsePermission : ObservationFibre
  publishedSandersSummary : ObservationFibre
  individualSandersPhases : ObservationFibre
  participantCrosswalk : ObservationFibre
  originalNiftiAndQC : ObservationFibre
  originalDataRights : ObservationFibre
  existingFiniteMotifToy : ObservationFibre
  prospectiveJointMeasure : ObservationFibre
  mechanisticM1a : ObservationFibre
  distinctiveM2 : ObservationFibre
  blindedHiddenTarget : ObservationFibre

data ObservationConsumer : Set where
  categoryProfileConsumer : ObservationConsumer
  recurrentMotifConsumer : ObservationConsumer
  publishedStudyComparison : ObservationConsumer
  pairedIndividualComparison : ObservationConsumer
  originalNeuralReplay : ObservationConsumer
  finiteToyNonidentification : ObservationConsumer
  mechanisticModelComparison : ObservationConsumer
  concealedInformationTest : ObservationConsumer

data AdmissibleIncidence :
  ObservationFibre → ObservationConsumer → Set where
  publishedToCategory :
    AdmissibleIncidence publishedErowidCategory categoryProfileConsumer

  timedReportToRecurrence :
    AdmissibleIncidence sequencedErowidReport recurrentMotifConsumer
  permissionToRecurrence :
    AdmissibleIncidence ErowidUsePermission recurrentMotifConsumer

  ErowidToPublishedComparison :
    AdmissibleIncidence publishedErowidCategory publishedStudyComparison
  SandersToPublishedComparison :
    AdmissibleIncidence publishedSandersSummary publishedStudyComparison

  timedReportToPaired :
    AdmissibleIncidence sequencedErowidReport pairedIndividualComparison
  permissionToPaired :
    AdmissibleIncidence ErowidUsePermission pairedIndividualComparison
  individualPhasesToPaired :
    AdmissibleIncidence individualSandersPhases pairedIndividualComparison
  overlapReceiptToPaired :
    AdmissibleIncidence participantCrosswalk pairedIndividualComparison

  voxelToOriginalReplay :
    AdmissibleIncidence originalNiftiAndQC originalNeuralReplay
  sourceRightsToOriginalReplay :
    AdmissibleIncidence originalDataRights originalNeuralReplay

  constructedToyToNonidentification :
    AdmissibleIncidence existingFiniteMotifToy finiteToyNonidentification

  measuredJointToModel :
    AdmissibleIncidence prospectiveJointMeasure mechanisticModelComparison
  measuredM1aToModel :
    AdmissibleIncidence mechanisticM1a mechanisticModelComparison
  measuredM2ToModel :
    AdmissibleIncidence distinctiveM2 mechanisticModelComparison

  blindedTargetToInformation :
    AdmissibleIncidence blindedHiddenTarget concealedInformationTest

------------------------------------------------------------------------
-- Existing hyperfabric record: status stalks, typed restriction/compatibility.
-- The identity restriction is deliberately only a status projection.
-- Equal status is NECESSARY in a global section, never SUFFICIENT evidence
-- of a sound experiment, agreement of observed values, or legal permission.
------------------------------------------------------------------------

motifEvidenceFabric :
  Fabric.TypedHyperfabric ObservationFibre ObservationConsumer
motifEvidenceFabric = record
  { vertexStalk = λ _ → Evidence.RecordStatus
  ; edgeStalk = λ _ → Evidence.RecordStatus
  ; incidence = AdmissibleIncidence
  ; restrict = λ _ status → status
  ; edgeProvenance = λ where
      categoryProfileConsumer →
        "Sean Noah; Miranda Shen; Earth Erowid; Fire Erowid; Michael Silver (2024), DOI 10.3389/fpsyg.2024.1397064" ∷ []
      recurrentMotifConsumer →
        "Erowid archival report chronology requires separate primary-report and authorised-use evidence, not present" ∷ []
      publishedStudyComparison →
        "Noah/Shen/Erowid/Silver (2024) DOI 10.3389/fpsyg.2024.1397064" ∷
        "Sanders et al. (2026) DOI 10.1093/nc/niag015; participant crosswalk unverified" ∷ []
      pairedIndividualComparison →
        "Original Erowid reports and Sanders individual-phase source, with permission and cohort-identity receipts unlocated" ∷ []
      originalNeuralReplay →
        "Christopher Timmermann et al. (2023) DOI 10.1073/pnas.2218949120; original voxel and QC not acquired" ∷ []
      finiteToyNonidentification →
        "DASHI.Biology.VisualMotifTransitionOperator; constructed symbolic recurrence, not fitted Erowid data" ∷ []
      mechanisticModelComparison →
        "Mago et al. (2026) DOI 10.1093/nc/niaf069; conceptual endogenous M1a source, not an empirical fit" ∷ []
      concealedInformationTest →
        "Future ethical preregistration and leakage-controlled acquisition required; no original study evidence" ∷ []
  ; edgeSalience = λ _ → 0
  ; fabricLabel = "DMT cross-source observation and rights hyperfabric"
  }

-- No edge from published proportions to within-report chronology, and
-- no original static-voxel transfer from retrospective report sentences.
staticCategoryCannotWitnessTransitions :
  AdmissibleIncidence publishedErowidCategory recurrentMotifConsumer → ⊥
staticCategoryCannotWitnessTransitions ()

staticCategoryCannotWitnessOriginalGFC :
  AdmissibleIncidence publishedErowidCategory originalNeuralReplay → ⊥
staticCategoryCannotWitnessOriginalGFC ()

toyCannotWitnessMechanisticFit :
  AdmissibleIncidence existingFiniteMotifToy mechanisticModelComparison → ⊥
toyCannotWitnessMechanisticFit ()

publishedPhasesCannotWitnessPairedCohorts :
  AdmissibleIncidence publishedSandersSummary pairedIndividualComparison → ⊥
publishedPhasesCannotWitnessPairedCohorts ()

------------------------------------------------------------------------
-- A concrete global-section incompatibility under different source-status
-- receipts. A report is NOT enough if its use authorization is unlocated.
------------------------------------------------------------------------

presentIsNotNotLocated :
  Evidence.present ≡ Evidence.notLocated → ⊥
presentIsNotNotLocated ()

reportTemporalNeedsPermission :
  (section : Fabric.GlobalSection motifEvidenceFabric) →
  Fabric.vertexValue section sequencedErowidReport ≡ Evidence.present →
  Fabric.vertexValue section ErowidUsePermission ≡ Evidence.notLocated →
  ⊥
reportTemporalNeedsPermission section reportPresent rightsUnlocated =
  presentIsNotNotLocated
    (trans (sym reportPresent)
      (trans (Fabric.compatible section timedReportToRecurrence)
        (trans
          (sym (Fabric.compatible section permissionToRecurrence))
          rightsUnlocated)))

------------------------------------------------------------------------
-- Same coarse motif *prevalence* is not the transition kernel.
-- This is a finite toy counterexample, not a claim of Erowid time-series
-- data or uniqueness of biological/cognitive hidden states.
------------------------------------------------------------------------

data ToyKernel : Set where
  stagnantKernel : ToyKernel
  cyclicKernel : ToyKernel

coarseOneTimeFrequency : ToyKernel → Nat
coarseOneTimeFrequency stagnantKernel = 3
coarseOneTimeFrequency cyclicKernel = 3

latticeToTunnelNumerator : ToyKernel → Nat
latticeToTunnelNumerator stagnantKernel = 0
latticeToTunnelNumerator cyclicKernel = 1

sameCoarseFrequency :
  coarseOneTimeFrequency stagnantKernel ≡
  coarseOneTimeFrequency cyclicKernel
sameCoarseFrequency = refl

differentTransition :
  latticeToTunnelNumerator stagnantKernel ≡
  latticeToTunnelNumerator cyclicKernel → ⊥
differentTransition ()

stationaryMarginalCounterexample :
  Evidence.HiddenCaseEvidence
    coarseOneTimeFrequency latticeToTunnelNumerator
stationaryMarginalCounterexample =
  Evidence.hiddenCaseEvidence
    stagnantKernel cyclicKernel
    sameCoarseFrequency differentTransition

noTransitionReconstructionFromCoarseFrequency :
  Evidence.ResidualDescendsThroughPublicLabel
    coarseOneTimeFrequency latticeToTunnelNumerator → ⊥
noTransitionReconstructionFromCoarseFrequency =
  Evidence.hiddenCaseEvidenceBlocksPublicDescent
    stationaryMarginalCounterexample

-- Compatibility with existing motif/ternary owners is source-typed reuse:
-- we import their finite definitions; no measured kernel or derived neural
-- identity is inferred from sharing a symbolic period.
originalMotifBoundary : Motif.MotifTransitionBoundary
originalMotifBoundary = Motif.canonicalMotifTransitionBoundary

originalNeuralObservationBoundary :
  NeuralQuotient.TernaryMotifNeuralBoundary
originalNeuralObservationBoundary =
  NeuralQuotient.canonicalTernaryMotifNeuralBoundary
