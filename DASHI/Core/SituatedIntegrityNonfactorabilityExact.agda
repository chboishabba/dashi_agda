module DASHI.Core.SituatedIntegrityNonfactorabilityExact where

------------------------------------------------------------------------
-- SITUATED INTEGRITY / NON-FACTORABILITY CROSS-POLLINATION
--
-- This bridge composes three existing owners rather than adding another
-- observer calculus:
--
--   DeclaredRealizedIntegrityResidualExact
--     owns declared-vs-realized social-ecology residuals;
--
--   IntersectionalNonFactorability
--     owns the generic theorem that a collision under a coarse observer blocks
--     factorisation, including after arbitrary post-composition/recharting;
--
--   SolisSituatedIntegrityBridgeExact
--     owns the bounded SCN control interpretation of the same synthetic
--     situated residual.
--
-- Cross-PR calibration:
--   PR #622 independently uses the same erased-coordinate/post-composition
--   theorem pattern for contextual alternatives; PR #624 uses it for
--   candidate-direction versus action-viability.  Those draft lanes are not
--   imported here.  The common mathematics stays owned by
--   IntersectionalNonFactorability.
--
-- The result relevant to the current social-ecology thread is exact:
--
--   same nominal public declaration
--   + same canonical person
--   + different realized ecology
--   => different situated residual
--   => different synthetic SCN action
--
-- and no relabelling/reweighting of the declared-access observer can recover
-- either erased distinction.
--
-- None of this says distress proves external system failure, that public-space
-- mismatch proves hostile intent, or that the SCN score is empirically
-- calibrated for autism.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.DeclaredRealizedIntegrityResidualExact as Integrity
import DASHI.Core.SolisSituatedIntegrityBridgeExact as Solis

------------------------------------------------------------------------
-- Fixed-person coarse observer and two downstream consumers.
------------------------------------------------------------------------

declaredOnlyObserver : Integrity.PublicEnvironment → Integrity.DeclaredAccess
declaredOnlyObserver environment =
  Integrity.declaredObservation Integrity.publicAccessObserver environment

situatedResidualObserver :
  Integrity.PublicEnvironment → Integrity.ResidualStatus
situatedResidualObserver environment =
  Integrity.integrityResidual
    Integrity.publicAccessObserver
    Integrity.canonicalPerson
    environment

situatedSCNObserver : Integrity.PublicEnvironment → Solis.SCNAction
situatedSCNObserver = Solis.situatedSCNAction

sameDeclaredObservation :
  declaredOnlyObserver Integrity.lowDemandThirdPlace
  ≡ declaredOnlyObserver Integrity.highDemandRestrictedSpace
sameDeclaredObservation = refl

residualsDiffer :
  situatedResidualObserver Integrity.lowDemandThirdPlace
  ≡ situatedResidualObserver Integrity.highDemandRestrictedSpace →
  ⊥
residualsDiffer ()

scnActionsDiffer :
  situatedSCNObserver Integrity.lowDemandThirdPlace
  ≡ situatedSCNObserver Integrity.highDemandRestrictedSpace →
  ⊥
scnActionsDiffer ()

------------------------------------------------------------------------
-- Exact non-factorability witnesses.
------------------------------------------------------------------------

declaredAccessCannotRecoverSituatedResidual :
  NF.NonFactorabilityWitness declaredOnlyObserver situatedResidualObserver
declaredAccessCannotRecoverSituatedResidual =
  NF.nonFactorabilityWitness
    Integrity.lowDemandThirdPlace
    Integrity.highDemandRestrictedSpace
    sameDeclaredObservation
    residualsDiffer

declaredAccessCannotRecoverSCNAction :
  NF.NonFactorabilityWitness declaredOnlyObserver situatedSCNObserver
declaredAccessCannotRecoverSCNAction =
  NF.nonFactorabilityWitness
    Integrity.lowDemandThirdPlace
    Integrity.highDemandRestrictedSpace
    sameDeclaredObservation
    scnActionsDiffer

noDeclaredAccessFactorisationForResidual :
  NF.FactorsThrough declaredOnlyObserver situatedResidualObserver → ⊥
noDeclaredAccessFactorisationForResidual =
  NF.witnessRulesOutEveryFlatFactorisation
    declaredAccessCannotRecoverSituatedResidual

noDeclaredAccessFactorisationForSCNAction :
  NF.FactorsThrough declaredOnlyObserver situatedSCNObserver → ⊥
noDeclaredAccessFactorisationForSCNAction =
  NF.witnessRulesOutEveryFlatFactorisation
    declaredAccessCannotRecoverSCNAction

------------------------------------------------------------------------
-- Arbitrary post-composition still cannot repair the erased coordinate.
-- This includes re-labelling, scalar scoring, weighting and other transforms
-- that consume only the already-collapsed declaration.
------------------------------------------------------------------------

rechartedDeclarationCannotRecoverResidual :
  ∀ {Recharted : Set} →
  (rechart : Integrity.DeclaredAccess → Recharted) →
  NF.FactorsThrough
    (λ environment → rechart (declaredOnlyObserver environment))
    situatedResidualObserver →
  ⊥
rechartedDeclarationCannotRecoverResidual rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart declaredAccessCannotRecoverSituatedResidual

rechartedDeclarationCannotRecoverSCNAction :
  ∀ {Recharted : Set} →
  (rechart : Integrity.DeclaredAccess → Recharted) →
  NF.FactorsThrough
    (λ environment → rechart (declaredOnlyObserver environment))
    situatedSCNObserver →
  ⊥
rechartedDeclarationCannotRecoverSCNAction rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart declaredAccessCannotRecoverSCNAction

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record SituatedIntegrityNonfactorabilityBoundary : Set where
  constructor situated-integrity-nonfactorability-boundary
  field
    declaredLabelDeterminesSituatedResidual : Bool
    declaredLabelDeterminesSituatedResidualIsFalse :
      declaredLabelDeterminesSituatedResidual ≡ false
    declaredLabelDeterminesSCNAction : Bool
    declaredLabelDeterminesSCNActionIsFalse :
      declaredLabelDeterminesSCNAction ≡ false
    postprocessingDeclaredLabelRepairsMissingEcology : Bool
    postprocessingDeclaredLabelRepairsMissingEcologyIsFalse :
      postprocessingDeclaredLabelRepairsMissingEcology ≡ false
    mismatchProvesHostileIntent : Bool
    mismatchProvesHostileIntentIsFalse : mismatchProvesHostileIntent ≡ false
    scnActionIsEmpiricalAutismDiagnosis : Bool
    scnActionIsEmpiricalAutismDiagnosisIsFalse :
      scnActionIsEmpiricalAutismDiagnosis ≡ false

canonicalSituatedIntegrityNonfactorabilityBoundary :
  SituatedIntegrityNonfactorabilityBoundary
canonicalSituatedIntegrityNonfactorabilityBoundary =
  situated-integrity-nonfactorability-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
