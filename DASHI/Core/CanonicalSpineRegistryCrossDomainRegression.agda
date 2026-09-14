module DASHI.Core.CanonicalSpineRegistryCrossDomainRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.CanonicalSpineRegistry as Registry

factorisationCanonical : Registry.CanonicalOwner
factorisationCanonical = Registry.factorisationOwner

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

appendOnlyCanonical : Registry.CanonicalOwner
appendOnlyCanonical = Registry.appendOnlyRevisionOwner

residualActionCanonical : Registry.CanonicalOwner
residualActionCanonical = Registry.residualActionPolicyOwner

genericReceiptCanonical : Registry.CanonicalOwner
genericReceiptCanonical = Registry.genericReceiptOwner

factorisationParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed factorisationCanonical ≡ false
factorisationParallelDefinitionsBlocked = refl

batchParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed batchCanonical ≡ false
batchParallelDefinitionsBlocked = refl

residualActionParallelDefinitionsBlocked :
  Registry.parallelDefinitionAllowed residualActionCanonical ≡ false
residualActionParallelDefinitionsBlocked = refl
