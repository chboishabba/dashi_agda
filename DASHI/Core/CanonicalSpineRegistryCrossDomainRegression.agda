module DASHI.Core.CanonicalSpineRegistryCrossDomainRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.CanonicalSpineRegistry as Registry

factorisationCanonical : Registry.CanonicalOwner
factorisationCanonical = Registry.factorisationOwner

queryIndexedProjectionCanonical : Registry.CanonicalOwner
queryIndexedProjectionCanonical = Registry.queryIndexedProjectionOwner

osintAcquisitionCanonical : Registry.CanonicalOwner
osintAcquisitionCanonical = Registry.osintAcquisitionOwner

boundedNegativeSearchCanonical : Registry.CanonicalOwner
boundedNegativeSearchCanonical = Registry.boundedNegativeSearchOwner

robustExperimentCanonical : Registry.CanonicalOwner
robustExperimentCanonical = Registry.robustExperimentInferenceOwner

multipartReconstructionCanonical : Registry.CanonicalOwner
multipartReconstructionCanonical = Registry.multipartReconstructionOwner

projectionFibreCanonical : Registry.CanonicalOwner
projectionFibreCanonical = Registry.projectionFibreOwner

consumerRepairCanonical : Registry.CanonicalOwner
consumerRepairCanonical = Registry.consumerFibreRepairOwner

candidateFamilyCanonical : Registry.CanonicalOwner
candidateFamilyCanonical = Registry.candidateFamilyExecutionOwner

batchCanonical : Registry.CanonicalOwner
batchCanonical = Registry.requirementConflictBatchOwner

localGlobalCanonical : Registry.CanonicalOwner
localGlobalCanonical = Registry.localGlobalGluingOwner

identityCanonical : Registry.CanonicalOwner
identityCanonical = Registry.candidateObjectIdentityOwner

attributionCanonical : Registry.CanonicalOwner
attributionCanonical = Registry.attributedSourceOwner

attributionSnowballCanonical : Registry.CanonicalOwner
attributionSnowballCanonical = Registry.attributionSnowballOwner

appendOnlyCanonical : Registry.CanonicalOwner
appendOnlyCanonical = Registry.appendOnlyRevisionOwner

residualActionCanonical : Registry.CanonicalOwner
residualActionCanonical = Registry.residualActionPolicyOwner

typedDependencyCanonical : Registry.CanonicalOwner
typedDependencyCanonical = Registry.typedDependencyOwner

genericReceiptCanonical : Registry.CanonicalOwner
genericReceiptCanonical = Registry.genericReceiptOwner

factorisationParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed factorisationCanonical ≡ false
factorisationParallelDefinitionsBlocked = refl

queryIndexedProjectionParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed queryIndexedProjectionCanonical ≡ false
queryIndexedProjectionParallelDefinitionsBlocked = refl

osintAcquisitionParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed osintAcquisitionCanonical ≡ false
osintAcquisitionParallelDefinitionsBlocked = refl

boundedNegativeSearchParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed boundedNegativeSearchCanonical ≡ false
boundedNegativeSearchParallelDefinitionsBlocked = refl

robustExperimentParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed robustExperimentCanonical ≡ false
robustExperimentParallelDefinitionsBlocked = refl

multipartReconstructionParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed multipartReconstructionCanonical ≡ false
multipartReconstructionParallelDefinitionsBlocked = refl

batchParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed batchCanonical ≡ false
batchParallelDefinitionsBlocked = refl

attributionSnowballParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed attributionSnowballCanonical ≡ false
attributionSnowballParallelDefinitionsBlocked = refl

residualActionParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed residualActionCanonical ≡ false
residualActionParallelDefinitionsBlocked = refl

typedDependencyParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed typedDependencyCanonical ≡ false
typedDependencyParallelDefinitionsBlocked = refl
