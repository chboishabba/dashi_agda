module DASHI.Physics.Plasma.ReducedKineticValidityClosureDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Generic reduced fluid-kinetic validity / closure owner.
-- Source:
-- N. F. Loureiro et al., "Viriato: A Fourier-Hermite spectral code for strongly magnetized fluid-kinetic plasma dynamics",
-- Computer Physics Communications 206 (2016) 45-63, DOI 10.1016/j.cpc.2016.05.004.
-- Viriato discusses KREHM as the Zocco-Schekochihin reduced model and states
-- the formal electron-beta ordering beta_e ~ m_e/m_i, while benchmarking some
-- behavior beyond the strict asymptotic regime.

data ValidityCoordinate : Set where
  strongGuideField : ValidityCoordinate
  electronBetaOrdering : ValidityCoordinate
  anisotropyOrdering : ValidityCoordinate
  electronInertiaRetained : ValidityCoordinate
  electronLandauDampingRetained : ValidityCoordinate
  ionFLREffectsRetained : ValidityCoordinate
  collisionModel : ValidityCoordinate
  resistivityModel : ValidityCoordinate
  velocitySpaceResolution : ValidityCoordinate
  hermiteTruncation : ValidityCoordinate
  hyperCollisionOrDissipation : ValidityCoordinate

record ReducedModelValidityProfile : Set where
  constructor reduced-model-validity-profile
  field
    coordinates : List ValidityCoordinate
    formalOrdering : String
    retainedPhysics : String
    excludedOrReducedPhysics : String
    sourceReference : String

open ReducedModelValidityProfile public

canonicalKREHMValidityProfile : ReducedModelValidityProfile
canonicalKREHMValidityProfile = reduced-model-validity-profile
  (strongGuideField ∷ electronBetaOrdering ∷ anisotropyOrdering ∷ electronInertiaRetained ∷ electronLandauDampingRetained ∷ ionFLREffectsRetained ∷ collisionModel ∷ resistivityModel ∷ velocitySpaceResolution ∷ hermiteTruncation ∷ hyperCollisionOrDissipation ∷ [])
  "formal KREHM ordering includes beta_e approximately m_e/m_i under a strong guide field"
  "phase mixing/Landau damping, electron inertia, selected ion finite-Larmor-radius effects, collisions and Ohmic resistivity are retained in the reduced description"
  "the model is an asymptotic reduction of fuller kinetic dynamics and is not universally valid for arbitrary beta/orderings"
  "Loureiro et al. 2016 DOI 10.1016/j.cpc.2016.05.004; KREHM model attribution therein"

record HermiteClosureState : Set where
  constructor hermite-closure-state
  field
    truncationIndex : String
    closureOrDissipation : String
    convergenceEvidence : String
    boundedReading : String

open HermiteClosureState public

canonicalHermiteClosureState : HermiteClosureState
canonicalHermiteClosureState = hermite-closure-state
  "finite maximum Hermite mode M"
  "finite velocity-space truncation requires a closure/dissipation strategy to control unresolved phase-space transfer"
  "resolution scans / benchmark agreement are required to distinguish converged dynamics from truncation artefacts"
  "More Hermite modes alone do not prove physical fidelity outside the reduced-model validity regime."

record ReducedModelBoundary : Set where
  constructor reduced-model-boundary
  field
    numericalConvergenceImpliesAsymptoticValidity : Bool
    numericalConvergenceImpliesAsymptoticValidityIsFalse : numericalConvergenceImpliesAsymptoticValidity ≡ false
    benchmarkAgreementImpliesUniversalApplicability : Bool
    benchmarkAgreementImpliesUniversalApplicabilityIsFalse : benchmarkAgreementImpliesUniversalApplicability ≡ false
    strictOrderingViolationImpliesNoQualitativeUsefulness : Bool
    strictOrderingViolationImpliesNoQualitativeUsefulnessIsFalse : strictOrderingViolationImpliesNoQualitativeUsefulness ≡ false
    closureChoiceCanAffectFiniteMResult : Bool
    closureChoiceCanAffectFiniteMResultIsTrue : closureChoiceCanAffectFiniteMResult ≡ true

open ReducedModelBoundary public

canonicalReducedModelBoundary : ReducedModelBoundary
canonicalReducedModelBoundary = reduced-model-boundary false refl false refl false refl true refl

data ReducedModelReverseTarget : Set where
  acquireTargetPlasmaOrdering : ReducedModelReverseTarget
  acquireBetaRegime : ReducedModelReverseTarget
  acquireNeglectedPhysicsEstimate : ReducedModelReverseTarget
  acquireHermiteResolutionScan : ReducedModelReverseTarget
  acquireClosureSensitivity : ReducedModelReverseTarget
  acquireCollisionSensitivity : ReducedModelReverseTarget
  acquireFullKineticComparison : ReducedModelReverseTarget
  acquireInvariantBudget : ReducedModelReverseTarget
