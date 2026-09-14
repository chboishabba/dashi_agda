{-# OPTIONS --safe #-}
module DASHI.Core.CanonicalSpineRegistry where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

data ProofStatus : Set where
  provedFinite : ProofStatus
  exactInterface : ProofStatus
  conditionalBridge : ProofStatus
  empiricalReceipt : ProofStatus
  openAnalyticTarget : ProofStatus

record CanonicalOwner : Set where
  constructor canonical-owner
  field
    concept : String
    moduleName : String
    status : ProofStatus
    parallelDefinitionAllowed : Bool
    parallelDefinitionAllowedIsFalse : parallelDefinitionAllowed ≡ false
open CanonicalOwner public

tritOwner : CanonicalOwner
tritOwner = canonical-owner "balanced ternary carrier" "DASHI.Algebra.Trit" provedFinite false refl

supportSignOwner : CanonicalOwner
supportSignOwner = canonical-owner "dependent support/sign factorisation" "DASHI.Algebra.TritSupportSignFactor" provedFinite false refl

multiscaleOwner : CanonicalOwner
multiscaleOwner = canonical-owner "multiscale carrier, residual, kernel, symmetry, and MDL step" "DASHI.Core.MultiscaleMDL" exactInterface false refl

ultrametricOwner : CanonicalOwner
ultrametricOwner = canonical-owner "369 prefix ultrametric" "DASHI.Geometry.SSP369Ultrametric" provedFinite false refl

mdlOwner : CanonicalOwner
mdlOwner = canonical-owner "MDL functional and Lyapunov contract" "DASHI.MDL.MDLLyapunov" exactInterface false refl

descentOwner : CanonicalOwner
descentOwner = canonical-owner "basin-local strict descent" "DASHI.Core.BasinFiniteDescent" exactInterface false refl

approximateNaturalityOwner : CanonicalOwner
approximateNaturalityOwner = canonical-owner "approximate multiscale kernel naturality" "DASHI.Core.ApproximateMultiscaleNaturality" exactInterface false refl

kernelSplitOwner : CanonicalOwner
kernelSplitOwner = canonical-owner "reversible evolution versus observation/dissipation" "DASHI.Core.ReversibleDissipativeKernelSplit" exactInterface false refl

codingTargetOwner : CanonicalOwner
codingTargetOwner = canonical-owner "source coding and rate-distortion targets" "DASHI.MDL.MultiscaleCodingTargets" openAnalyticTarget false refl

continuumTargetOwner : CanonicalOwner
continuumTargetOwner = canonical-owner "discrete-continuum, metric, and action targets" "DASHI.Physics.DiscreteContinuumKernelTargets" openAnalyticTarget false refl

factorisationOwner : CanonicalOwner
factorisationOwner = canonical-owner "consumer-relative factorisation, descent, sufficiency, and non-descent" "DASHI.Core.ConsumerDescentMinimalObserverExact" exactInterface false refl

queryIndexedProjectionOwner : CanonicalOwner
queryIndexedProjectionOwner = canonical-owner
  "query-indexed projection adequacy and exact query-specific collision"
  "DASHI.Core.QueryIndexedProjectionAdequacyExact"
  exactInterface false refl

experimentalCoordinateOwner : CanonicalOwner
experimentalCoordinateOwner = canonical-owner
  "experimental coordinate roles, declared control-relative invariance, derived-discriminator provenance, and collision-separating coordinates"
  "DASHI.Core.ExperimentalCoordinateDesignExact"
  exactInterface false refl

osintAcquisitionOwner : CanonicalOwner
osintAcquisitionOwner = canonical-owner
  "OSINT acquisition, source/carrier identity, corroboration independence, and search-nonlocation firewall"
  "DASHI.Core.SnowballOSINTAcquisitionInvariantExact"
  exactInterface false refl

boundedNegativeSearchOwner : CanonicalOwner
boundedNegativeSearchOwner = canonical-owner
  "proof-valued bounded negative search refining the OSINT nonlocation firewall with an explicit universe-coverage gate for global absence"
  "DASHI.Core.BoundedNegativeSearchExact"
  exactInterface false refl

robustExperimentInferenceOwner : CanonicalOwner
robustExperimentInferenceOwner = canonical-owner
  "robust experiment frontier separating training fit, held-out repair, model adequacy, and experiment design"
  "DASHI.Core.RobustExperimentInferenceFrontierExact"
  exactInterface false refl

multipartReconstructionOwner : CanonicalOwner
multipartReconstructionOwner = canonical-owner
  "complete multipart reconstruction with indexed part admission, compatibility, and explicit whole same-object receipt"
  "DASHI.Core.MultipartSameObjectReconstructionExact"
  exactInterface false refl

projectionFibreOwner : CanonicalOwner
projectionFibreOwner = canonical-owner "coarse/fine projection with retained relative-fine fibre and exact reopening" "DASHI.Core.CoarseFineRelativeFibreExact" exactInterface false refl

consumerFibreRepairOwner : CanonicalOwner
consumerFibreRepairOwner = canonical-owner "consumer-relative collision repair by observer refinement" "DASHI.Core.ConsumerFibreRepairExact" exactInterface false refl

frozenProvenanceDynamicOwner : CanonicalOwner
frozenProvenanceDynamicOwner = canonical-owner
  "provenance-aware strict refinement with frozen selection and separate dynamic-safety payment"
  "DASHI.Core.FrozenProvenanceDynamicRefinementExact"
  exactInterface false refl

queryIndexedFutureSafePromotionOwner : CanonicalOwner
queryIndexedFutureSafePromotionOwner = canonical-owner
  "query-indexed future-safe promotion requiring frozen provenance-aware refinement, query adequacy, and dynamic safety"
  "DASHI.Core.QueryIndexedFrozenDynamicPromotionExact"
  exactInterface false refl

candidateFamilyExecutionOwner : CanonicalOwner
candidateFamilyExecutionOwner = canonical-owner "selected candidate-family admissibility, composition, and independent global execution check" "DASHI.Core.CandidateFamilyExecutionExact" exactInterface false refl

requirementConflictBatchOwner : CanonicalOwner
requirementConflictBatchOwner = canonical-owner "requirement-closed, conflict-free batch execution with independent global validity" "DASHI.Core.RequirementConflictBatchExecutionExact" exactInterface false refl

localGlobalGluingOwner : CanonicalOwner
localGlobalGluingOwner = canonical-owner "compatible local family, gluing, global section, and exact restriction-back" "DASHI.Foundations.StageValuationBundleAtlas" exactInterface false refl

candidateObjectIdentityOwner : CanonicalOwner
candidateObjectIdentityOwner = canonical-owner "graded candidate same-object identity and exact identity receipt" "DASHI.Core.KnowledgeBoundaryCandidateIdentityBidiExact" exactInterface false refl

attributedSourceOwner : CanonicalOwner
attributedSourceOwner = canonical-owner "attributed source identity, DOI state, source role, visibility, and authority firewall" "DASHI.Core.AttributedSourceCore" exactInterface false refl

attributionSnowballOwner : CanonicalOwner
attributionSnowballOwner = canonical-owner "snowball retention of source identity, source role, visibility, proof non-import, and authority non-creation" "DASHI.Core.SnowballAttributionProvenanceInvariantExact" exactInterface false refl

appendOnlyRevisionOwner : CanonicalOwner
appendOnlyRevisionOwner = canonical-owner "append-only evidence history with non-monotone conclusion and residual revision" "DASHI.Core.AppendOnlyEvidenceResidualRevisionExact" exactInterface false refl

residualActionPolicyOwner : CanonicalOwner
residualActionPolicyOwner = canonical-owner "typed residual-to-action policy with proof-bearing admission and least-privilege authority boundary" "DASHI.Core.ResidualActionPolicyExact" exactInterface false refl

typedDependencyOwner : CanonicalOwner
typedDependencyOwner = canonical-owner "typed dependency witnesses, indexed requirement families, and admissible dependent actions" "DASHI.Core.TypedDependencyCore" exactInterface false refl

genericReceiptOwner : CanonicalOwner
genericReceiptOwner = canonical-owner "generic non-promoting receipt metadata and list-level fail-closed receipt proof" "DASHI.Core.GenericReceipt" exactInterface false refl

canonicalOwners : List CanonicalOwner
canonicalOwners =
  tritOwner ∷ supportSignOwner ∷ multiscaleOwner ∷ ultrametricOwner ∷ mdlOwner ∷
  descentOwner ∷ approximateNaturalityOwner ∷ kernelSplitOwner ∷ codingTargetOwner ∷
  continuumTargetOwner ∷ factorisationOwner ∷ queryIndexedProjectionOwner ∷
  experimentalCoordinateOwner ∷ osintAcquisitionOwner ∷ boundedNegativeSearchOwner ∷
  robustExperimentInferenceOwner ∷ multipartReconstructionOwner ∷ projectionFibreOwner ∷
  consumerFibreRepairOwner ∷ frozenProvenanceDynamicOwner ∷
  queryIndexedFutureSafePromotionOwner ∷ candidateFamilyExecutionOwner ∷
  requirementConflictBatchOwner ∷ localGlobalGluingOwner ∷ candidateObjectIdentityOwner ∷
  attributedSourceOwner ∷ attributionSnowballOwner ∷ appendOnlyRevisionOwner ∷
  residualActionPolicyOwner ∷ typedDependencyOwner ∷ genericReceiptOwner ∷ []

record RepositoryClosureBoundary : Set where
  constructor repository-closure-boundary
  field
    canonicalOwnersRecorded : Bool
    canonicalOwnersRecordedIsTrue : canonicalOwnersRecorded ≡ true
    crossDomainOwnersRecorded : Bool
    crossDomainOwnersRecordedIsTrue : crossDomainOwnersRecorded ≡ true
    everythingCompileConfirmedHere : Bool
    everythingCompileConfirmedHereIsFalse : everythingCompileConfirmedHere ≡ false
    duplicateOwnersEliminatedAutomatically : Bool
    duplicateOwnersEliminatedAutomaticallyIsFalse : duplicateOwnersEliminatedAutomatically ≡ false
    registryEntryMakesEveryDomainManifestationDefinitionallyIdentical : Bool
    registryEntryMakesEveryDomainManifestationDefinitionallyIdenticalIsFalse :
      registryEntryMakesEveryDomainManifestationDefinitionallyIdentical ≡ false
open RepositoryClosureBoundary public

canonicalRepositoryClosureBoundary : RepositoryClosureBoundary
canonicalRepositoryClosureBoundary =
  repository-closure-boundary true refl true refl false refl false refl false refl
