module DASHI.Biology.Agriculture.DrylandPioneerLegumeGrasslandRegenerationHyperfabricRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.DrylandPioneerLegumeGrasslandRegenerationHyperfabricExact as H

sameRoleNotSameObject : H.sameFunctionalRoleCreatesSameEcologicalObject H.canonicalRegenerationHyperfabricBoundary ≡ false
sameRoleNotSameObject = refl

roleNotTransfer : H.sameFunctionalRoleCreatesTransferableResponse H.canonicalRegenerationHyperfabricBoundary ≡ false
roleNotTransfer = refl

t1NotT2 : H.interventionSuccessAtT1ImpliesTrajectorySuccessAtT2 H.canonicalRegenerationHyperfabricBoundary ≡ false
t1NotT2 = refl

pioneerNotEndpoint : H.pioneerEstablishmentImpliesDesiredSuccessionalEndpoint H.canonicalRegenerationHyperfabricBoundary ≡ false
pioneerNotEndpoint = refl

pioneerDominanceNotRelease : H.pioneerDominanceImpliesSuccessfulSuccessionalRelease H.canonicalRegenerationHyperfabricBoundary ≡ false
pioneerDominanceNotRelease = refl

richnessNotComposition : H.referenceLikeRichnessImpliesReferenceLikeComposition H.canonicalRegenerationHyperfabricBoundary ≡ false
richnessNotComposition = refl

chronosequenceNotCausalTrajectory : H.chronosequenceAgeGradientImpliesLongitudinalCausalRecovery H.canonicalRegenerationHyperfabricBoundary ≡ false
chronosequenceNotCausalTrajectory = refl

microbiomeNotWholeEcosystem : H.microbiomeReferenceSimilarityImpliesWholeEcosystemRecovery H.canonicalRegenerationHyperfabricBoundary ≡ false
microbiomeNotWholeEcosystem = refl

disturbanceRegimeRetained : H.disturbanceRegimeMustRemainIndexed H.canonicalRegenerationHyperfabricBoundary ≡ true
disturbanceRegimeRetained = refl

nurseNotNativeRecovery : H.temporaryNurseFunctionImpliesNativeCommunityRecovery H.canonicalRegenerationHyperfabricBoundary ≡ false
nurseNotNativeRecovery = refl

sourceIdentityRetained : H.sourceSystemIdentityMustRemainIndexed H.canonicalRegenerationHyperfabricBoundary ≡ true
sourceIdentityRetained = refl
