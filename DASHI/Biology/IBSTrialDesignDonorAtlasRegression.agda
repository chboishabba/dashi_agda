module DASHI.Biology.IBSTrialDesignDonorAtlasRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Biology.IBSTrialDesignDonorAtlasExact as Donor

atlasRegression : Donor.canonicalIBSTrialDesignDonorAtlas ≡ Donor.canonicalIBSTrialDesignDonorAtlas
atlasRegression = refl

smartNotIBSEvidenceRegression : Donor.SMARTDesignProvesIBSEfficacyPermission → ⊥
smartNotIBSEvidenceRegression = Donor.smartDesignDoesNotProveIBSEfficacy

nOf1NotUniversalRegression : Donor.NOf1ResultAutomaticallyGeneralizesPermission → ⊥
nOf1NotUniversalRegression = Donor.nOf1DoesNotAutomaticallyGeneralize

cleNotTargetingRegression : Donor.CLEReactionIsValidatedFoodTargetPermission → ⊥
cleNotTargetingRegression = Donor.cleReactionDoesNotValidateFoodTarget
