module DASHI.Physics.YangMills.BalabanClayExternalModelAndFailureAuditExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayLiteralFrontierQuarantinedClaims as Quarantine
import DASHI.Physics.YangMills.BalabanClayNumericalIngredientDependencyAuditExact as Numerical

------------------------------------------------------------------------
-- External proposals are recorded as audit targets, never theorem premises.
------------------------------------------------------------------------

data ExternalAuditClass : Set where
  modelSuitabilityAudit adversarialFailureAnalysis unverifiedObstructionClaim
  completionClaimQuarantine : ExternalAuditClass

record ExternalAuditEntry : Set where
  constructor external
  field
    authorsOrSite : String
    titleOrScope : String
    venue : String
    stableIdentifier : String
    classification : ExternalAuditClass
    admissibleAsAuthority : Bool
    usableAsRiskPrompt : Bool
    theoryFieldContent : String
    exactAuditQuestion : String
    requiredTransferOrReproduction : String

open ExternalAuditEntry public

uidtSuitability : ExternalAuditEntry
uidtSuitability = external
  "UIDT authors / Mass-Gap project"
  "Unified Information-Density Theory and later covariant scalar-field versions"
  "Mendeley Data, SSRN and associated repositories"
  "Mendeley dataset kc8cmw9p2w; SSRN abstract 5807202"
  modelSuitabilityAudit
  false
  true
  "Yang--Mills coupled to an additional information-density scalar S(x), not the pure-gauge field content"
  "Are gamma, kappa, integer exponents, dimensional anchors, normalisations and dataset choices theorem-derived, calibrated or selected?"
  "A separately proved pure-sector decoupling/transfer theorem and a complete numerical dependency graph"

massGapCircularityAnalysis : ExternalAuditEntry
massGapCircularityAnalysis = external
  "Unverified Zenodo author submission"
  "The Yang--Mills Mass Gap: From Proof Attempts to Dissolution by Recontextualisation"
  "Zenodo"
  "10.5281/zenodo.19423313"
  adversarialFailureAnalysis
  false
  true
  "purports to analyse pure Yang--Mills proof routes"
  "Does any correlation-length estimate used by DASHI already assume the spectral gap it is intended to prove?"
  "Independent reproduction of every claimed obstruction; no obstruction is accepted as a theorem"

record MassGapDependencyAcyclicityReceipt : Set₁ where
  field
    RGContraction ExponentialClustering OSReconstruction SpectralGap : Set
    rgToClustering : RGContraction → ExponentialClustering
    clusteringToOS : ExponentialClustering → OSReconstruction
    osToGap : OSReconstruction → SpectralGap
    noGapAssumptionInRGContraction : Set
    noClusteringAssumptionInRGContraction : Set
    everyDecayConstantHasUpstreamOwner : Set
    dependencyGraphAcyclic : Set

open MassGapDependencyAcyclicityReceipt public

record UIDTNumericalSuitabilityReceipt : Set₁ where
  field
    numericalAudit : Numerical.ExternalModelNumericalAudit
    gammaDefinitionOwner : String
    kappaDependencyOwner : String
    integerExponentDerivationOwner : String
    dimensionalAnchorOwners : List String
    fittingData : List String
    withheldData : List String
    fitAndWithheldDataDisjoint : Set
    pureYangMillsTransferTheorem : Set
    noClaimOfClayRelevanceWithoutTransfer : Set

open UIDTNumericalSuitabilityReceipt public

externalAuditEntries : List ExternalAuditEntry
externalAuditEntries = uidtSuitability ∷ massGapCircularityAnalysis ∷ []

externalAuditVocabularyLevel : ProofLevel
externalAuditVocabularyLevel = machineChecked

massGapAcyclicityReceiptDefinitionLevel : ProofLevel
massGapAcyclicityReceiptDefinitionLevel = machineChecked

uidtNumericalAndPureSectorAuditInputsLevel : ProofLevel
uidtNumericalAndPureSectorAuditInputsLevel = conditional

massGapDependencyAcyclicityInputsLevel : ProofLevel
massGapDependencyAcyclicityInputsLevel = conditional
