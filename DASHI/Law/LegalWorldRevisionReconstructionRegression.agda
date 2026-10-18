module DASHI.Law.LegalWorldRevisionReconstructionRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.LegalWorldRevisionReconstructionExact as World

boundary : World.LegalWorldRevisionReconstructionBoundary
boundary = World.canonicalLegalWorldRevisionReconstructionBoundary

worldCarriesCoordinates :
  World.legalWorldCarriesTimeJurisdictionAndRevision boundary ≡ true
worldCarriesCoordinates =
  World.legalWorldCarriesTimeJurisdictionAndRevisionIsTrue boundary

validityIsWorldRelative :
  World.authorityValidityIsWorldRelative boundary ≡ true
validityIsWorldRelative =
  World.authorityValidityIsWorldRelativeIsTrue boundary

jurisdictionMustMatch :
  World.jurisdictionAxisMustMatchQueryWorld boundary ≡ true
jurisdictionMustMatch =
  World.jurisdictionAxisMustMatchQueryWorldIsTrue boundary

revisionReopensDirect :
  World.sourceRevisionMayReopenDirectDependents boundary ≡ true
revisionReopensDirect =
  World.sourceRevisionMayReopenDirectDependentsIsTrue boundary

revisionReopensCone :
  World.sourceRevisionMayReopenProofConeTransitively boundary ≡ true
revisionReopensCone =
  World.sourceRevisionMayReopenProofConeTransitivelyIsTrue boundary

revisionDoesNotRefute :
  World.revisionAutomaticallyRefutesPriorEvidence boundary ≡ false
revisionDoesNotRefute =
  World.revisionAutomaticallyRefutesPriorEvidenceIsFalse boundary

revisionCreatesNoTruth :
  World.revisionReopeningCreatesClaimTruth boundary ≡ false
revisionCreatesNoTruth =
  World.revisionReopeningCreatesClaimTruthIsFalse boundary
