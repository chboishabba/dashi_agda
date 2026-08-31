module DASHI.Culture.IntellectualReceptionIntersectionalInformationGeometryExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / INTERSECTIONAL INFORMATION GEOMETRY
--
-- This module cross-pollinates the reception support/demand lane with the
-- canonical intersectional non-factorability and constraint-interaction owners.
--
-- Source boundary:
-- Crenshaw motivates the warning against reconstructing situated joint states
-- from isolated axes.  The finite reception information carrier, its codes and
-- its factorisation theorems below are DASHI mathematics, not propositions
-- attributed to Crenshaw.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Culture.IntellectualReceptionSupportDemandFarCrossPollinationExact as Far
import DASHI.Culture.IntellectualReceptionSharedObservedPrefixCertificateReuseExact as Reuse
import DASHI.Culture.IntellectualReceptionConsumerObservationDemandPreorderExact as Demand

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.IntersectionalConstraintGeometryExact as Intersection
import DASHI.Core.IntersectionalBinaryInteractionBridgeExact as Interaction

------------------------------------------------------------------------
-- 1. A situated multi-axis information carrier.
--
-- These are synthetic information situations used to demonstrate that support,
-- demand, provenance and authority are independent axes.  They are not claims
-- about empirical populations or social groups.
------------------------------------------------------------------------

data InformationSituation : Set where
  presentFutureInherited
  authorityInherited
  authorityIntroduced
  presentFutureIntroduced
  : InformationSituation

data SupportClass : Set where
  presentFutureSupportClass authoritySupportClass : SupportClass

data DemandClass : Set where
  stage2DemandClass beyondFiltrationDemandClass : DemandClass

data ProvenanceClass : Set where
  inheritedProvenance introducedProvenance : ProvenanceClass

data AuthorityClass : Set where
  authorityAbsent authorityPresent : AuthorityClass

data SituatedInformationCode : Set where
  pfInheritedCode
  authorityInheritedCode
  authorityIntroducedCode
  pfIntroducedCode
  : SituatedInformationCode

supportClass : InformationSituation → SupportClass
supportClass presentFutureInherited = presentFutureSupportClass
supportClass authorityInherited = authoritySupportClass
supportClass authorityIntroduced = authoritySupportClass
supportClass presentFutureIntroduced = presentFutureSupportClass

demandClass : InformationSituation → DemandClass
demandClass presentFutureInherited = beyondFiltrationDemandClass
demandClass authorityInherited = stage2DemandClass
demandClass authorityIntroduced = stage2DemandClass
demandClass presentFutureIntroduced = beyondFiltrationDemandClass

provenanceClass : InformationSituation → ProvenanceClass
provenanceClass presentFutureInherited = inheritedProvenance
provenanceClass authorityInherited = inheritedProvenance
provenanceClass authorityIntroduced = introducedProvenance
provenanceClass presentFutureIntroduced = introducedProvenance

authorityClass : InformationSituation → AuthorityClass
authorityClass presentFutureInherited = authorityAbsent
authorityClass authorityInherited = authorityPresent
authorityClass authorityIntroduced = authorityPresent
authorityClass presentFutureIntroduced = authorityAbsent

situatedInformationCode : InformationSituation → SituatedInformationCode
situatedInformationCode presentFutureInherited = pfInheritedCode
situatedInformationCode authorityInherited = authorityInheritedCode
situatedInformationCode authorityIntroduced = authorityIntroducedCode
situatedInformationCode presentFutureIntroduced = pfIntroducedCode

------------------------------------------------------------------------
-- 2. Every isolated axis has a collision that the situated carrier separates.
------------------------------------------------------------------------

supportAxisWitness :
  INF.NonFactorabilityWitness supportClass situatedInformationCode
supportAxisWitness =
  INF.nonFactorabilityWitness
    authorityInherited
    authorityIntroduced
    refl
    (λ ())

supportAxisCannotRecoverSituatedInformation :
  INF.FactorsThrough supportClass situatedInformationCode → ⊥
supportAxisCannotRecoverSituatedInformation =
  INF.witnessRulesOutEveryFlatFactorisation supportAxisWitness

demandAxisWitness :
  INF.NonFactorabilityWitness demandClass situatedInformationCode
demandAxisWitness =
  INF.nonFactorabilityWitness
    authorityInherited
    authorityIntroduced
    refl
    (λ ())

demandAxisCannotRecoverSituatedInformation :
  INF.FactorsThrough demandClass situatedInformationCode → ⊥
demandAxisCannotRecoverSituatedInformation =
  INF.witnessRulesOutEveryFlatFactorisation demandAxisWitness

provenanceAxisWitness :
  INF.NonFactorabilityWitness provenanceClass situatedInformationCode
provenanceAxisWitness =
  INF.nonFactorabilityWitness
    presentFutureInherited
    authorityInherited
    refl
    (λ ())

provenanceAxisCannotRecoverSituatedInformation :
  INF.FactorsThrough provenanceClass situatedInformationCode → ⊥
provenanceAxisCannotRecoverSituatedInformation =
  INF.witnessRulesOutEveryFlatFactorisation provenanceAxisWitness

authorityAxisWitness :
  INF.NonFactorabilityWitness authorityClass situatedInformationCode
authorityAxisWitness =
  INF.nonFactorabilityWitness
    authorityInherited
    authorityIntroduced
    refl
    (λ ())

authorityAxisCannotRecoverSituatedInformation :
  INF.FactorsThrough authorityClass situatedInformationCode → ⊥
authorityAxisCannotRecoverSituatedInformation =
  INF.witnessRulesOutEveryFlatFactorisation authorityAxisWitness

------------------------------------------------------------------------
-- 3. Recharting a collapsed single axis cannot repair the missing joint state.
------------------------------------------------------------------------

rechartedSupportCannotRecoverSituatedInformation :
  ∀ {Chart : Set} →
  (rechart : SupportClass → Chart) →
  INF.FactorsThrough
    (λ state → rechart (supportClass state))
    situatedInformationCode → ⊥
rechartedSupportCannotRecoverSituatedInformation rechart =
  INF.rechartingCannotRecoverErasedPhenomenon rechart supportAxisWitness

rechartedDemandCannotRecoverSituatedInformation :
  ∀ {Chart : Set} →
  (rechart : DemandClass → Chart) →
  INF.FactorsThrough
    (λ state → rechart (demandClass state))
    situatedInformationCode → ⊥
rechartedDemandCannotRecoverSituatedInformation rechart =
  INF.rechartingCannotRecoverErasedPhenomenon rechart demandAxisWitness

------------------------------------------------------------------------
-- 4. The concrete reception support/demand reversal is an intersectional-style
-- obstruction to one-dimensional information quality.
------------------------------------------------------------------------

canonicalSupportDemandReversal : Far.SupportInclusionDemandReversal
canonicalSupportDemandReversal = Far.canonicalSupportInclusionDemandReversal

authoritySupportStillNoMoreObservationDemanding :
  Demand.ConsumerNoMoreObservationDemanding
    Reuse.authoritySensitiveSupport
    Reuse.presentFutureSupport
authoritySupportStillNoMoreObservationDemanding =
  Demand.authorityNoMoreDemandingThanPresentFuture

-- Strict support growth and lower separation demand coexist.
record CrossedInformationAxes : Set where
  constructor crossed-information-axes
  field
    supportGrows :
      Far.StrictSupportIncluded
        Reuse.presentFutureSupport
        Reuse.authoritySensitiveSupport
    observationDemandFalls :
      Demand.ConsumerNoMoreObservationDemanding
        Reuse.authoritySensitiveSupport
        Reuse.presentFutureSupport
    reverseDemandFails :
      Demand.ConsumerNoMoreObservationDemanding
        Reuse.presentFutureSupport
        Reuse.authoritySensitiveSupport → ⊥

canonicalCrossedInformationAxes : CrossedInformationAxes
canonicalCrossedInformationAxes =
  crossed-information-axes
    Far.presentFutureStrictlyIncludedInAuthority
    Demand.authorityNoMoreDemandingThanPresentFuture
    Demand.presentFutureNotNoMoreDemandingThanAuthority

------------------------------------------------------------------------
-- 5. Reuse canonical intersectional constraint geometry literally.
--
-- The imported theorem says a held-fixed single axis cannot recover a joint
-- constraint state and that scalar depth is not primary intersectional
-- semantics.  We do not identify social constraint geometry with reception
-- information geometry; the theorem shape is the cross-domain precedent.
------------------------------------------------------------------------

intersectionalSingleAxisNonFactorabilityRetained :
  INF.FactorsThrough
    Intersection.sexualityAxis
    Intersection.jointConstraint → ⊥
intersectionalSingleAxisNonFactorabilityRetained =
  Intersection.sexualityAxisCannotRecoverJointConstraint

intersectionalRechartingBoundaryRetained :
  ∀ {Chart : Set} →
  (rechart : Intersection.SexualityAxisObservation → Chart) →
  INF.FactorsThrough
    (λ state → rechart (Intersection.sexualityAxis state))
    Intersection.jointConstraint → ⊥
intersectionalRechartingBoundaryRetained =
  Intersection.rechartedSexualityAxisCannotRecoverJointConstraint

intersectionalJointInteractionNotMarginalConjunction :
  Intersection.marginalPublicRecognition Intersection.jointAxes
  ≡ Intersection.interactionPublicRecognition Intersection.jointAxes → ⊥
intersectionalJointInteractionNotMarginalConjunction =
  Intersection.jointInteractionIsNotRecoveredByMarginalConjunction

------------------------------------------------------------------------
-- 6. Reuse the generic binary interaction / rectangle obstruction.
--
-- This is stronger than saying two axes are both relevant: the joint response
-- cannot be reconstructed by endpoint-additive potentials in the canonical
-- finite intersectional specimen.
------------------------------------------------------------------------

intersectionalRectangleObstructionRetained :
  Interaction.IntersectionalInteractionAdmission
intersectionalRectangleObstructionRetained =
  Interaction.canonicalIntersectionalInteractionAdmission

------------------------------------------------------------------------
-- 7. No scalar-information-quality promotion.
--
-- We prove this for each candidate one-axis flattening above.  We do NOT claim
-- the impossible theorem that every function into Nat loses information: an
-- injective encoding could trivially enumerate this finite carrier.  The point
-- is semantic: support size, separation demand, provenance or authority alone
-- do not recover the situated information state.
------------------------------------------------------------------------

data SupportScalarIsCompleteInformationQuality : Set where
data DemandScalarIsCompleteInformationQuality : Set where
data ProvenanceScalarIsCompleteInformationQuality : Set where
data AuthorityScalarIsCompleteInformationQuality : Set where

data IntersectionalAnalogyIdentifiesDomains : Set where
data ReceptionInformationCodeIsOppressionScale : Set where
data CrenshawAuthoredReceptionInformationTheorem : Set where

supportScalarDoesNotBecomeCompleteInformationQuality :
  SupportScalarIsCompleteInformationQuality → ⊥
supportScalarDoesNotBecomeCompleteInformationQuality ()

demandScalarDoesNotBecomeCompleteInformationQuality :
  DemandScalarIsCompleteInformationQuality → ⊥
demandScalarDoesNotBecomeCompleteInformationQuality ()

provenanceScalarDoesNotBecomeCompleteInformationQuality :
  ProvenanceScalarIsCompleteInformationQuality → ⊥
provenanceScalarDoesNotBecomeCompleteInformationQuality ()

authorityScalarDoesNotBecomeCompleteInformationQuality :
  AuthorityScalarIsCompleteInformationQuality → ⊥
authorityScalarDoesNotBecomeCompleteInformationQuality ()

intersectionalAnalogyDoesNotIdentifyDomains :
  IntersectionalAnalogyIdentifiesDomains → ⊥
intersectionalAnalogyDoesNotIdentifyDomains ()

receptionInformationCodeIsNotOppressionScale :
  ReceptionInformationCodeIsOppressionScale → ⊥
receptionInformationCodeIsNotOppressionScale ()

crenshawNotCreditedWithReceptionInformationTheorem :
  CrenshawAuthoredReceptionInformationTheorem → ⊥
crenshawNotCreditedWithReceptionInformationTheorem ()

------------------------------------------------------------------------
-- 8. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionIntersectionalInformationGeometryBoundary : Set where
  constructor intellectual-reception-intersectional-information-geometry-boundary
  field
    supportAloneRecoversSituatedInformation : Bool
    demandAloneRecoversSituatedInformation : Bool
    provenanceAloneRecoversSituatedInformation : Bool
    authorityAloneRecoversSituatedInformation : Bool
    rechartingCollapsedAxisRepairsMissingJointInformation : Bool
    supportAndDemandCanMoveInOppositeDirections : Bool
    canonicalIntersectionalJointNonfactorabilityRetained : Bool
    canonicalIntersectionalNonlinearInteractionRetained : Bool
    scalarDepthIsPrimaryIntersectionalSemantics : Bool
    receptionInformationCodeIsUniversalOppressionScale : Bool
    crenshawCreditedWithReceptionInformationTheorem : Bool
    sourceAttributionBoundarySurvivesIntersectionalCrossPollination : Bool

canonicalIntellectualReceptionIntersectionalInformationGeometryBoundary :
  IntellectualReceptionIntersectionalInformationGeometryBoundary
canonicalIntellectualReceptionIntersectionalInformationGeometryBoundary =
  intellectual-reception-intersectional-information-geometry-boundary
    false false false false false true true true false false false true
