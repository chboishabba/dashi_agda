module DASHI.Biology.KitzerowBH4MaxCutValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.KitzerowBH4CascadeExact as Cascade
import DASHI.Biology.KitzerowBH4RepoIntegrationExact as Integration
import DASHI.Biology.KitzerowBH4SourceAtlasExact as Sources
import DASHI.Biology.KitzerowBH4ConvergentEvidenceExact as Evidence
import DASHI.Biology.KitzerowPriorityAttributionExact as Attribution
import DASHI.Biology.KitzerowBH4PriorArtSubtractionExact as PriorArt
import DASHI.Biology.KitzerowBH4ExperimentalDiscriminatorExact as Experiment
import DASHI.Biology.KitzerowBH4ParetoAcquisitionExact as Pareto

candidateGraphDoesNotClaimWholeModelConfirmation :
  Cascade.wholeModelConfirmed Cascade.canonicalKitzerowBH4Cascade ≡ false
candidateGraphDoesNotClaimWholeModelConfirmation = refl

repoIntegrationConsumesBiologyBrainChemistry :
  Integration.consumesBiologyCore Integration.canonicalKitzerowBH4RepoIntegration ≡ true
  × Integration.consumesBrainNeurochemicalCore Integration.canonicalKitzerowBH4RepoIntegration ≡ true
  × Integration.consumesChemistryBiologyInterop Integration.canonicalKitzerowBH4RepoIntegration ≡ true
repoIntegrationConsumesBiologyBrainChemistry = refl , refl , refl

repoIntegrationKeepsPromotionBlocked :
  Integration.promotesClinicalAuthority Integration.canonicalKitzerowBH4RepoIntegration ≡ false
  × Integration.promotesBrainStateRecovery Integration.canonicalKitzerowBH4RepoIntegration ≡ false
repoIntegrationKeepsPromotionBlocked = refl , refl

allCurrentEvidenceReceiptsRejectWholeModelConfirmation :
  Evidence.allCanonicalEvidenceReceiptsRejectWholeModelConfirmation ≡ true
allCurrentEvidenceReceiptsRejectWholeModelConfirmation = refl

stanfordContactIsNotSilentlyVerified :
  Attribution.stanfordDirectContactVerified Attribution.canonicalStanfordAttribution ≡ false
stanfordContactIsNotSilentlyVerified = refl

japanBoundedIndependenceIsRetained :
  Attribution.derivation Attribution.canonicalNomuraAttribution ≡ Attribution.independentDerivationSupported
japanBoundedIndependenceIsRetained = refl

priorArtPartitionSeparatesInheritedBiology :
  PriorArt.inheritedPriorBiologyRetained PriorArt.canonicalNomuraPriorArtPartition ≡ true
priorArtPartitionSeparatesInheritedBiology = refl

centralBH4AllocationRemainsExperimentallyOpen :
  Experiment.centralBH4AllocationClosed Experiment.canonicalCentralBH4Discriminator ≡ false
centralBH4AllocationRemainsExperimentallyOpen = refl

paretoFrontierIsNotTruthRanking :
  Pareto.frontierRankIsTruthRank Pareto.canonicalKitzerowAcquisitionFrontier ≡ false
paretoFrontierIsNotTruthRanking = refl
