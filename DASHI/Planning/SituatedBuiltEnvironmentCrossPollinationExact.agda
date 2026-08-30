module DASHI.Planning.SituatedBuiltEnvironmentCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Architecture.AgentRelativeAffordanceExact as Architecture
import DASHI.Biology.SocialEcologicalAffordanceConeExact as Ecology
import DASHI.Core.EpistemicInquiryGovernance as Inquiry
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as LES
import DASHI.Governance.BritishColumbiaDecriminalizationBundleExact as BC
import DASHI.Governance.OppositionInterfaceAntiDomesticationExact as Opposition
import DASHI.Planning.PlanningRepresentationDescentExact as Descent

------------------------------------------------------------------------
-- SITUATED BUILT ENVIRONMENT CROSS-POLLINATION
--
-- Planning/architecture is not modeled as geometry alone.  This module keeps
-- one thin spatial carrier over independently existing theorem owners for:
--
--   * architecture-level geometry / agent-relative usability;
--   * social-ecological realised affordance;
--   * management-history / ecology / provenance / justice hyperfabric;
--   * epistemic participation and constitutive authority;
--   * anti-domestication of admitted opposition;
--   * policy-bundle / public-space phase distinctions;
--   * planning-representation non-factorability.
--
-- The point is composition, not replacement.  All substantive non-collapse
-- theorems remain owned by their source modules.
------------------------------------------------------------------------

record SituatedBuiltEnvironment : Set₁ where
  constructor situatedBuiltEnvironment
  field
    architecturalDesign : Descent.Design
    socialEcology : Ecology.Ecology
    socioEcologicalHistory : LES.FullLESSituatedState

open SituatedBuiltEnvironment public

PlanningSurface : Set
PlanningSurface =
  Descent.PlanningEnvelope ×
  (Ecology.BuiltEnvironment × LES.FullCoarseObservation)

planningSurface : SituatedBuiltEnvironment → PlanningSurface
planningSurface state =
  Descent.planningProjection (architecturalDesign state) ,
    (Ecology.built (socialEcology state) ,
      LES.fullCoarseObservation (socioEcologicalHistory state))

SituatedConsumerSignature : Set
SituatedConsumerSignature =
  Descent.HeatExposure × LES.FullPlanningSignature

situatedConsumerSignature :
  SituatedBuiltEnvironment → SituatedConsumerSignature
situatedConsumerSignature state =
  Descent.heatExposure (architecturalDesign state) ,
    LES.fullPlanningSignature (socioEcologicalHistory state)

------------------------------------------------------------------------
-- Concrete lifted planning-representation failure.
--
-- The planning surface can preserve a coarse envelope, the same built-space
-- category and the same coarse socio-ecological observation while erasing an
-- architecture-level consumer distinction.
------------------------------------------------------------------------

sameSituatedContextShaded : SituatedBuiltEnvironment
sameSituatedContextShaded =
  situatedBuiltEnvironment
    Descent.shadedCourtyard
    Ecology.sameBuiltSpacePermissive
    LES.shortIsolatedIndigenous

sameSituatedContextExposed : SituatedBuiltEnvironment
sameSituatedContextExposed =
  situatedBuiltEnvironment
    Descent.exposedCourtyard
    Ecology.sameBuiltSpacePermissive
    LES.shortIsolatedIndigenous

sameCoarseSituatedPlanningSurface :
  planningSurface sameSituatedContextShaded ≡
  planningSurface sameSituatedContextExposed
sameCoarseSituatedPlanningSurface = refl

situatedConsumerSignaturesDiffer :
  situatedConsumerSignature sameSituatedContextShaded ≡
  situatedConsumerSignature sameSituatedContextExposed → ⊥
situatedConsumerSignaturesDiffer ()

situatedBuiltEnvironmentNonFactorability :
  INF.NonFactorabilityWitness planningSurface situatedConsumerSignature
situatedBuiltEnvironmentNonFactorability =
  INF.nonFactorabilityWitness
    sameSituatedContextShaded
    sameSituatedContextExposed
    sameCoarseSituatedPlanningSurface
    situatedConsumerSignaturesDiffer

coarseSituatedPlanningSurfaceCannotRecoverConsumerSignature :
  INF.FactorsThrough planningSurface situatedConsumerSignature → ⊥
coarseSituatedPlanningSurfaceCannotRecoverConsumerSignature =
  INF.witnessRulesOutEveryFlatFactorisation
    situatedBuiltEnvironmentNonFactorability

rechartingCoarseSituatedSurfaceCannotRepairErasedConsumer :
  ∀ {Recharted : Set} →
  (rechart : PlanningSurface → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (planningSurface state))
    situatedConsumerSignature →
  ⊥
rechartingCoarseSituatedSurfaceCannotRepairErasedConsumer rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart situatedBuiltEnvironmentNonFactorability

------------------------------------------------------------------------
-- Existing theorem owners remain live at the planning seam.
------------------------------------------------------------------------

geometryDoesNotDetermineAgentRelativeUsability :
  Architecture.Affords Architecture.architectureAffordanceSystem
    Architecture.stairOnlyConnection Architecture.stepFreeUser
    Architecture.reachUpperLevel → ⊥
geometryDoesNotDetermineAgentRelativeUsability =
  Architecture.notUsableForOtherAgent

institutionCanAlterRealisedConeWithoutRebuildingGeometry :
  Ecology.institution Ecology.sameBuiltSpacePermissive ≡
  Ecology.institution Ecology.sameBuiltSpaceRestrictive → ⊥
institutionCanAlterRealisedConeWithoutRebuildingGeometry =
  Ecology.institutionCanChangeConeWithoutRebuildingSpace

restrictiveEffectDoesNotManufactureDesignIntent :
  Ecology.RestrictiveEffectImpliesIntentPermission → ⊥
restrictiveEffectDoesNotManufactureDesignIntent =
  Ecology.restrictiveEffectDoesNotAutoProveIntent

policyLabelDoesNotDetermineImplementationBundle :
  BC.DecriminalizationLabelPromotesFullBundle → ⊥
policyLabelDoesNotDetermineImplementationBundle =
  BC.labelDoesNotPromoteFullBundle

admittedOppositionDoesNotManufactureMetaRuleAuthority :
  Opposition.CanAlterAdmissionRule Opposition.recognisedOpposition → ⊥
admittedOppositionDoesNotManufactureMetaRuleAuthority =
  Opposition.recognisedOppositionCannotAutomaticallyAlterRule

voiceDoesNotManufacturePlanningConstitutiveAuthority :
  (coordinate : Inquiry.InquiryCoordinate) →
  Inquiry.Authorised Inquiry.canonicalDemoGovernance
    Inquiry.demoStudent coordinate → ⊥
voiceDoesNotManufacturePlanningConstitutiveAuthority =
  Inquiry.voiceDoesNotManufactureConstitutiveAuthority

------------------------------------------------------------------------
-- Boundary: this is a structural planning carrier, not a claim that every
-- real planning process instantiates every listed axis or source theorem.
------------------------------------------------------------------------

record SituatedBuiltEnvironmentBoundary : Set where
  constructor situatedBuiltEnvironmentBoundary
  field
    geometryAloneDeterminesRealisedAccess : Bool
    policyLabelDeterminesImplementationBundle : Bool
    consultationAutomaticallyCreatesMetaRulePower : Bool
    participantExpressionAutomaticallyCreatesConstitutiveAuthority : Bool
    coarsePlanningSurfaceCanAlwaysRecoverSituatedConsumer : Bool

canonicalSituatedBuiltEnvironmentBoundary : SituatedBuiltEnvironmentBoundary
canonicalSituatedBuiltEnvironmentBoundary =
  situatedBuiltEnvironmentBoundary false false false false false
