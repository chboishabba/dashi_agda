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

nurseNotNativeRecovery : H.temporaryNurseFunctionImpliesNativeCommunityRecovery H.canonicalRegenerationHyperfabricBoundary ≡ false
temporaryNurseNotNativeRecovery = refl

sourceIdentityRetained : H.sourceSystemIdentityMustRemainIndexed H.canonicalRegenerationHyperfabricBoundary ≡ true
sourceIdentityRetained = refl
