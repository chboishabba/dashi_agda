module DASHI.Governance.EpistemicCaptureProfessionalClosureExact where

------------------------------------------------------------------------
-- EPISTEMIC CAPTURE / PROFESSIONAL CLOSURE
--
-- This module formalizes two related but distinct mechanisms:
--   (1) cheap production of authority-signalling surfaces can collide under a
--       coarse observer even when underlying validity differs;
--   (2) an institution can control the public admission/legibility interface
--       without thereby exhausting independently constituted source carriers.
--
-- It reuses observer-refinement and contested-ambient-interface owners.  The
-- historical Church/legal-profession discussion motivates the architecture;
-- no theorem below attributes motive or a live empirical classification to a
-- named profession, court, church or political actor.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.ContestedAmbientAuthorityHyperformalismExact as Ambient
import DASHI.Interop.PNFHyperfabric369 as Hyperfabric

------------------------------------------------------------------------
-- 1. Authority-signalling surface != authority-bearing reasoning.
------------------------------------------------------------------------

data ArgumentState : Set where
  professionallyValidatedArgument aiPseudoArgument : ArgumentState

data FormalSurface : Set where
  polishedLegalSurface : FormalSurface

data ValidationSurface : Set where
  validatedSurface invalidSurface : ValidationSurface

formalSurfaceObserver : Observer.Observer ArgumentState FormalSurface
formalSurfaceObserver _ = polishedLegalSurface

validationObserver : Observer.Observer ArgumentState ValidationSurface
validationObserver professionallyValidatedArgument = validatedSurface
validationObserver aiPseudoArgument = invalidSurface

authoritySignalCollision : Observer.ObserverCollision formalSurfaceObserver
authoritySignalCollision =
  Observer.observerCollision
    professionallyValidatedArgument
    aiPseudoArgument
    refl
    (λ ())

authoritySurfaceIsNotSeparating : Observer.Separating formalSurfaceObserver → ⊥
authoritySurfaceIsNotSeparating =
  Observer.collisionBlocksSeparation authoritySignalCollision

validationStrictlyRefinesFormalSurface :
  Observer.StrictRefinement formalSurfaceObserver validationObserver
validationStrictlyRefinesFormalSurface =
  Observer.strictRefinement
    (λ x y equality → refl)
    professionallyValidatedArgument
    aiPseudoArgument
    refl
    (λ ())

------------------------------------------------------------------------
-- 2. Closure can migrate from production to validation.
------------------------------------------------------------------------

data ProfessionalGate : Set where
  productionGate validationGate : ProfessionalGate

record ClosureConfiguration : Set where
  constructor closureConfiguration
  field
    productionRestricted : Bool
    validationRestricted : Bool

preGenerativeClosure : ClosureConfiguration
preGenerativeClosure = closureConfiguration true true

postGenerativeClosure : ClosureConfiguration
postGenerativeClosure = closureConfiguration false true

productionBarrierFallsWhileValidationBarrierRemains :
  ClosureConfiguration.productionRestricted postGenerativeClosure ≡ false
  × ClosureConfiguration.validationRestricted postGenerativeClosure ≡ true
productionBarrierFallsWhileValidationBarrierRemains = refl , refl

record ProfessionalClosureMigrationWitness : Set where
  constructor professionalClosureMigrationWitness
  field
    before : ClosureConfiguration
    after : ClosureConfiguration
    beforeProductionRestricted :
      ClosureConfiguration.productionRestricted before ≡ true
    afterProductionOpen :
      ClosureConfiguration.productionRestricted after ≡ false
    afterValidationRestricted :
      ClosureConfiguration.validationRestricted after ≡ true

canonicalProfessionalClosureMigration : ProfessionalClosureMigrationWitness
canonicalProfessionalClosureMigration =
  professionalClosureMigrationWitness
    preGenerativeClosure
    postGenerativeClosure
    refl refl refl

------------------------------------------------------------------------
-- 3. Ambient legibility/admission is not ontology.
--
-- A captured admission regime requires every publicly admitted source state to
-- be represented by the declared interface.  The existing anti-sublation
-- exterior witness proves that such a regime cannot admit an independently
-- authoritative exterior state without first changing/refining its interface.
------------------------------------------------------------------------

record InterfaceAdmissionRegime
    {leftCarrier rightCarrier : Ambient.NormativeCarrier}
    (interface : Ambient.TypedInterface leftCarrier rightCarrier) : Set₁ where
  constructor interfaceAdmissionRegime
  field
    PubliclyAdmitted : Ambient.State leftCarrier → Set
    admissionRequiresRepresentation :
      (state : Ambient.State leftCarrier) →
      PubliclyAdmitted state →
      Σ (Ambient.Meet interface)
        (λ meet → Ambient.left interface meet ≡ state)

open InterfaceAdmissionRegime public

canonicalRepresentationBoundRegime :
  InterfaceAdmissionRegime Ambient.canonicalPartialInterface
canonicalRepresentationBoundRegime =
  interfaceAdmissionRegime
    (λ state → Σ Ambient.SharedMeet
      (λ meet → Ambient.left Ambient.canonicalPartialInterface meet ≡ state))
    (λ state admitted → admitted)

exteriorCannotBeAdmittedByRepresentationBoundRegime :
  PubliclyAdmitted canonicalRepresentationBoundRegime Ambient.sourceExterior → ⊥
exteriorCannotBeAdmittedByRepresentationBoundRegime admitted with
  admissionRequiresRepresentation
    canonicalRepresentationBoundRegime
    Ambient.sourceExterior
    admitted
... | meet , represented =
  Ambient.ExteriorWitness.notRepresented Ambient.canonicalExterior meet represented

-- The failure is in this admission interface.  It is not a theorem that the
-- source state itself is absent, false or without independent authority.
exteriorStateStillExistsInSourceCarrier : Ambient.State Ambient.sourceCarrier
exteriorStateStillExistsInSourceCarrier = Ambient.sourceExterior

exteriorStateRetainsIndependentAuthoritySource : Authority.AuthoritySource
exteriorStateRetainsIndependentAuthoritySource =
  Ambient.IndependentlyAuthoritativeExterior.independentAuthoritySource
    Ambient.canonicalIndependentExterior

exteriorIndependentAuthoritySourceIsAdmissible :
  Authority.AdmissibleAuthoritySource exteriorStateRetainsIndependentAuthoritySource
exteriorIndependentAuthoritySourceIsAdmissible =
  Ambient.IndependentlyAuthoritativeExterior.independentAuthorityAdmissible
    Ambient.canonicalIndependentExterior

------------------------------------------------------------------------
-- 4. Epistemic capture as monopoly over the authoritative meta-observer.
------------------------------------------------------------------------

record AuthoritativeMetaObserverCapture
    {Source PublicSurface : Set}
    (publicObserver : Source → PublicSurface) : Set₁ where
  constructor authoritativeMetaObserverCapture
  field
    AdmissiblePublicState : Source → Set
    publicAdmissionFactorsThroughObserver :
      (state : Source) → AdmissiblePublicState state → PublicSurface
    observerOwnsPublicClassification : Bool
    unobservedStateMayStillExist : Bool

open AuthoritativeMetaObserverCapture public

canonicalMetaObserverCapture :
  AuthoritativeMetaObserverCapture formalSurfaceObserver
canonicalMetaObserverCapture =
  authoritativeMetaObserverCapture
    (λ state → validationObserver state ≡ validatedSurface)
    (λ state admitted → formalSurfaceObserver state)
    true
    true

-- Even under the public meta-observer, two source states can remain collapsed.
metaObserverCaptureDoesNotMakeSurfaceSeparating :
  Observer.Separating formalSurfaceObserver → ⊥
metaObserverCaptureDoesNotMakeSurfaceSeparating = authoritySurfaceIsNotSeparating

------------------------------------------------------------------------
-- 5. Recognition and force still do not self-issue authority.
------------------------------------------------------------------------

externalRecognitionCannotCloseAuthorityGap :
  Authority.AdmissibleAuthoritySource Authority.externalRecognitionAlone →
  Authority.Never
externalRecognitionCannotCloseAuthorityGap = Authority.externalRecognitionAloneRejected

forceCannotCloseAuthorityGap :
  Authority.AdmissibleAuthoritySource Authority.possessionOfForce →
  Authority.Never
forceCannotCloseAuthorityGap = Authority.possessionOfForceRejected

------------------------------------------------------------------------
-- 6. Shared hyperformal representation is a meeting fabric, not a sovereign
--    meta-ontology.
------------------------------------------------------------------------

hyperformalMeetingFabricDoesNotPromoteAuthority :
  (object : Hyperfabric.HyperfabricObject) →
  Hyperfabric.hyperfabricPromotesExternalTheorem object ≡ false
hyperformalMeetingFabricDoesNotPromoteAuthority =
  Hyperfabric.hyperfabricDoesNotPromoteExternalTheorem

------------------------------------------------------------------------
-- 7. Boundary.
------------------------------------------------------------------------

record EpistemicCaptureProfessionalClosureBoundary : Set where
  constructor epistemicCaptureProfessionalClosureBoundary
  field
    polishedSurfaceImpliesValidatedReasoning : Bool
    cheapProductionImpliesCheapValidation : Bool
    publicLegibilityExhaustsSourceOntology : Bool
    interfaceNonAdmissionImpliesSourceNonexistence : Bool
    recognitionCreatesAuthority : Bool
    coerciveDominanceCreatesAuthority : Bool
    sharedHyperformalCarrierCreatesSovereignMetaOntology : Bool
    productionClosureCanMigrateToValidationClosure : Bool
    publicMetaObserverCanRemainNonSeparating : Bool
    sourceExteriorCanRemainIndependentlyAuthoritative : Bool

canonicalEpistemicCaptureProfessionalClosureBoundary :
  EpistemicCaptureProfessionalClosureBoundary
canonicalEpistemicCaptureProfessionalClosureBoundary =
  epistemicCaptureProfessionalClosureBoundary
    false false false false false false false true true true

epistemicCaptureProfessionalClosureStatement : String
epistemicCaptureProfessionalClosureStatement =
  "Commodity production of formal prose can destroy the old production signal while leaving validation/refinement professionally scarce. A dominant institution may control the public legibility/admission interface, but non-admission through that interface does not annihilate an independently constituted source carrier or manufacture the institution's authority. Shared hyperformal geometry remains a meeting fabric rather than a sovereign meta-ontology."
