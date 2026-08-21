module DASHI.Governance.ContestedAmbientAuthorityHyperformalismExact where

------------------------------------------------------------------------
-- CONTESTED AMBIENT AUTHORITY / ANTI-SUBLATION HYPERFORMALISM
--
-- Thin convergence layer over existing theorem owners.  The only genuinely
-- new primitive here is a symmetric typed interface between independently
-- constituted carriers.  No carrier is declared the ambient/host carrier by
-- construction.  Authority, admissibility, coercion, PNF typed-meet failure,
-- justice non-factorability, peace-domain scope, sublation boundaries and the
-- 369 hyperfabric no-promotion law are imported from their existing owners.
--
-- The intended discipline is:
--
--   * no host by type declaration;
--   * NO_TYPED_MEET is not source annihilation;
--   * interface recognition is not exhaustive source representation;
--   * recognition alone is not authority;
--   * coercive dominance is not legitimate ambient authority;
--   * internal/order projections do not automatically determine justice;
--   * shared hyperformal carrier geometry does not promote external authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as Intersectional
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.ClosedAuthorityInverseJusticeExact as ClosedAuthority
import DASHI.Governance.ContestabilityAccessCostExact as Contestability
import DASHI.Governance.DomainIndexedPeaceSubjectCarrier as Peace
import DASHI.Governance.SituatedInverseJusticeFibreExact as Justice
import DASHI.Governance.TraumaMemorySublationBoundary as Sublation
import DASHI.Interop.InspectionRelativeNoTypedMeet as NoMeet
import DASHI.Interop.PNFHyperfabric369 as Hyperfabric
import DASHI.Interop.PNFVoidScopeBoundary as VoidScope

------------------------------------------------------------------------
-- 1. Independently constituted carriers and symmetric partial interfaces.
------------------------------------------------------------------------

record NormativeCarrier : Set₁ where
  constructor normativeCarrier
  field
    State : Set
    carrierLabel : String

open NormativeCarrier public

record TypedInterface (leftCarrier rightCarrier : NormativeCarrier) : Set₁ where
  constructor typedInterface
  field
    Meet : Set
    left : Meet → State leftCarrier
    right : Meet → State rightCarrier

open TypedInterface public

-- A left-total interface would represent every source state inside the
-- declared meet surface.  This is a property to prove, never a default.
record LeftExhaustive
  {leftCarrier rightCarrier : NormativeCarrier}
  (interface : TypedInterface leftCarrier rightCarrier) : Set where
  constructor leftExhaustive
  field
    represent : State leftCarrier → Meet interface
    representExact :
      (state : State leftCarrier) →
      left interface (represent state) ≡ state

open LeftExhaustive public

-- An exterior witness is a source state for which this interface contains no
-- representing meet.  The source state remains a perfectly ordinary member of
-- its own carrier.
record ExteriorWitness
  {leftCarrier rightCarrier : NormativeCarrier}
  (interface : TypedInterface leftCarrier rightCarrier) : Set where
  constructor exteriorWitness
  field
    exteriorState : State leftCarrier
    notRepresented :
      (meet : Meet interface) →
      left interface meet ≡ exteriorState →
      ⊥

open ExteriorWitness public

-- Strengthen exteriority with an authority source that is independently
-- admissible under the existing AuthorityMandateCore.  Recognition by the
-- other carrier is therefore not the thing that manufactures the source's
-- authority witness.
record IndependentlyAuthoritativeExterior
  {leftCarrier rightCarrier : NormativeCarrier}
  (interface : TypedInterface leftCarrier rightCarrier) : Set where
  constructor independentlyAuthoritativeExterior
  field
    exterior : ExteriorWitness interface
    independentAuthoritySource : Authority.AuthoritySource
    independentAuthorityAdmissible :
      Authority.AdmissibleAuthoritySource independentAuthoritySource

open IndependentlyAuthoritativeExterior public

interfaceExhaustionContradictsIndependentExterior :
  ∀ {leftCarrier rightCarrier}
    {interface : TypedInterface leftCarrier rightCarrier} →
  LeftExhaustive interface →
  IndependentlyAuthoritativeExterior interface →
  ⊥
interfaceExhaustionContradictsIndependentExterior exhaustive independent =
  notRepresented (exterior independent)
    (represent exhaustive (exteriorState (exterior independent)))
    (representExact exhaustive (exteriorState (exterior independent)))

------------------------------------------------------------------------
-- 2. Finite canonical witness: an interface can be real and nonempty while
--    still leaving an independently authoritative source state outside it.
------------------------------------------------------------------------

data SourceState : Set where
  sourceExterior sourceShared : SourceState

data OtherState : Set where
  otherShared : OtherState

data SharedMeet : Set where
  sharedMeet : SharedMeet

sourceCarrier : NormativeCarrier
sourceCarrier = normativeCarrier SourceState "independent source carrier"

otherCarrier : NormativeCarrier
otherCarrier = normativeCarrier OtherState "other institutional carrier"

canonicalPartialInterface : TypedInterface sourceCarrier otherCarrier
canonicalPartialInterface =
  typedInterface
    SharedMeet
    (λ { sharedMeet → sourceShared })
    (λ { sharedMeet → otherShared })

canonicalExterior : ExteriorWitness canonicalPartialInterface
canonicalExterior =
  exteriorWitness
    sourceExterior
    (λ { sharedMeet () })

canonicalIndependentExterior :
  IndependentlyAuthoritativeExterior canonicalPartialInterface
canonicalIndependentExterior =
  independentlyAuthoritativeExterior
    canonicalExterior
    Authority.constituencyMandate
    tt

canonicalInterfaceIsNotSourceExhaustive :
  LeftExhaustive canonicalPartialInterface → ⊥
canonicalInterfaceIsNotSourceExhaustive exhaustive =
  interfaceExhaustionContradictsIndependentExterior
    exhaustive
    canonicalIndependentExterior

-- This is the anti-sublation core: a successful shared interface need not
-- consume or exhaust the independently authoritative source carrier.
recognitionInterfaceDoesNotExhaustSourceCarrier :
  LeftExhaustive canonicalPartialInterface → ⊥
recognitionInterfaceDoesNotExhaustSourceCarrier =
  canonicalInterfaceIsNotSourceExhaustive

------------------------------------------------------------------------
-- 3. Ambient/hosthood is a claim with a source, not a primitive embedding.
------------------------------------------------------------------------

data ContestedContext : Set where
  contestedContext : ContestedContext

record AmbientAuthorityClaim (carrier : NormativeCarrier) : Set where
  constructor ambientAuthorityClaim
  field
    ambientContext : ContestedContext
    claimedSource : Authority.AuthoritySource
    coercivelyDominant : Bool

open AmbientAuthorityClaim public

LegitimateAmbientAuthority :
  ∀ {carrier} → AmbientAuthorityClaim carrier → Set
LegitimateAmbientAuthority claim =
  Authority.AdmissibleAuthoritySource (claimedSource claim)

-- A coercively dominant claim can be represented without being granted
-- legitimacy.  Existing AuthorityMandateCore rejects possession of force as
-- an admissible authority source.
forceDominantAmbientClaim : AmbientAuthorityClaim otherCarrier
forceDominantAmbientClaim =
  ambientAuthorityClaim
    contestedContext
    Authority.possessionOfForce
    true

coerciveDominanceDoesNotEstablishLegitimateAmbientAuthority :
  LegitimateAmbientAuthority forceDominantAmbientClaim → Authority.Never
coerciveDominanceDoesNotEstablishLegitimateAmbientAuthority =
  Authority.possessionOfForceRejected

-- External recognition is likewise explicitly rejected as a self-issuing
-- source of authority by the pre-existing authority core.
recognitionAloneDoesNotCreateAmbientAuthority :
  Authority.AdmissibleAuthoritySource Authority.externalRecognitionAlone →
  Authority.Never
recognitionAloneDoesNotCreateAmbientAuthority =
  Authority.externalRecognitionAloneRejected

-- A source-side claim may have an independently admissible source without any
-- theorem saying that it thereby defeats the other claim.  The point here is
-- simply that claims coexist before an ambient carrier is chosen.
sourceAmbientClaim : AmbientAuthorityClaim sourceCarrier
sourceAmbientClaim =
  ambientAuthorityClaim
    contestedContext
    Authority.constituencyMandate
    false

sourceAmbientClaimHasAdmissibleSource :
  LegitimateAmbientAuthority sourceAmbientClaim
sourceAmbientClaimHasAdmissibleSource = tt

record ContestedAmbientPair : Set where
  constructor contestedAmbientPair
  field
    sourceClaim : AmbientAuthorityClaim sourceCarrier
    otherClaim : AmbientAuthorityClaim otherCarrier

canonicalContestedAmbientPair : ContestedAmbientPair
canonicalContestedAmbientPair =
  contestedAmbientPair sourceAmbientClaim forceDominantAmbientClaim

------------------------------------------------------------------------
-- 4. NO_TYPED_MEET remains inspection-relative and non-annihilating.
--
-- The imported PNF owners already prove that no-typed-meet does not promote
-- truth, support, admissibility, global impossibility or permanent
-- incommensurability.  We compose that with the exterior witness: the source
-- state remains outside the interface regardless of a current-inspection
-- typed-meet failure.
------------------------------------------------------------------------

noTypedMeetStillDoesNotPromoteGlobalImpossibility :
  NoMeet.GlobalNoTypedMeetClaim.globalImpossibilityPromoted
    NoMeet.canonicalGlobalNoTypedMeetClaim
  ≡ false
noTypedMeetStillDoesNotPromoteGlobalImpossibility =
  NoMeet.noTypedMeetAtCurrentInspectionNoGlobalImpossibility

noTypedMeetStillDoesNotPromotePermanentIncommensurability :
  NoMeet.GlobalNoTypedMeetClaim.permanentIncommensurabilityPromoted
    NoMeet.canonicalGlobalNoTypedMeetClaim
  ≡ false
noTypedMeetStillDoesNotPromotePermanentIncommensurability =
  NoMeet.noTypedMeetAtCurrentInspectionNoPermanentIncommensurability

noTypedMeetStillDoesNotPromoteTruth :
  NoMeet.NoTypedMeetAtInspection.truthPromotion
    NoMeet.canonicalNoTypedMeetAtCurrentInspection
  ≡ false
noTypedMeetStillDoesNotPromoteTruth =
  NoMeet.noTypedMeetAtCurrentInspectionNoTruthPromotion

noTypedMeetStillDoesNotPromoteAdmissibility :
  NoMeet.NoTypedMeetAtInspection.admissibilityPromotion
    NoMeet.canonicalNoTypedMeetAtCurrentInspection
  ≡ false
noTypedMeetStillDoesNotPromoteAdmissibility =
  NoMeet.noTypedMeetAtCurrentInspectionNoAdmissibilityPromotion

outsideComparisonStillDoesNotPromoteTruth :
  VoidScope.boundaryStatusPromotesTruth
    VoidScope.outsideComparison_scopeExceeded
  ≡ false
outsideComparisonStillDoesNotPromoteTruth =
  VoidScope.boundaryStatusTruthGateFalse
    VoidScope.outsideComparison_scopeExceeded

canonicalExteriorSurvivesCurrentNoTypedMeet :
  NoMeet.NoTypedMeetAtInspection →
  ExteriorWitness canonicalPartialInterface
canonicalExteriorSurvivesCurrentNoTypedMeet _ = canonicalExterior

------------------------------------------------------------------------
-- 5. Existing justice / peace / sublation / closed-authority theorems remain
--    the owners of their respective claims.  This module only welds them into
--    the contested-ambient picture.
------------------------------------------------------------------------

orderLikeFlatProjectionCannotDetermineSituatedJustice :
  Intersectional.FactorsThrough
    Intersectional.flatProjection
    Intersectional.relationalOutcome →
  ⊥
orderLikeFlatProjectionCannotDetermineSituatedJustice =
  Justice.intersectionalFlatteningCannotDetermineJusticeSign

formalContestabilityStillDoesNotEstablishAffordableJusticeAccess :
  Contestability.AffordableContestability
    Contestability.finiteCost
    Contestability.finiteBudget →
  ⊥
formalContestabilityStillDoesNotEstablishAffordableJusticeAccess =
  Justice.formalContestabilityDoesNotEstablishAffordableJusticeAccess

-- Domain-specific peace/de-escalation cannot be silently promoted to a global
-- moral or political property.
domainPeaceStillDoesNotAutomaticallyGlobalise :
  ∀ {P actor domain} {peace : Peace.PeaceAt P actor domain} →
  Peace.DomainPeaceAutomaticallyGlobal peace → ⊥
domainPeaceStillDoesNotAutomaticallyGlobalise =
  Peace.domainPeaceDoesNotAutomaticallyGlobalise

formalSublationStillDoesNotGuaranteeReconciliation :
  Sublation.formalSublationGuaranteesReconciliation
    Sublation.canonicalTraumaMemoryCrossPollination
  ≡ false
formalSublationStillDoesNotGuaranteeReconciliation =
  Sublation.formalSublationDoesNotGuaranteeReconciliation
    Sublation.canonicalTraumaMemorySublationBoundary

closedCorrectionFailureCanCoexistWithRepeatedInverseJustice :
  ClosedAuthority.ClosedAuthorityInverseJusticeStabilisation
closedCorrectionFailureCanCoexistWithRepeatedInverseJustice =
  ClosedAuthority.closedAuthorityCanStabiliseInverseJustice

------------------------------------------------------------------------
-- 6. Shared 369/hyperformal geometry is explicitly non-sovereign.
------------------------------------------------------------------------

sharedHyperformalCarrierDoesNotPromoteExternalTheorem :
  (object : Hyperfabric.HyperfabricObject) →
  Hyperfabric.hyperfabricPromotesExternalTheorem object ≡ false
sharedHyperformalCarrierDoesNotPromoteExternalTheorem =
  Hyperfabric.hyperfabricDoesNotPromoteExternalTheorem

monsterLabelInSharedFabricStillDoesNotPromoteExternalTheorem :
  Hyperfabric.hyperfabricPromotesExternalTheorem
    Hyperfabric.wheelEarthSpokePrimeCarrier
  ≡ false
monsterLabelInSharedFabricStillDoesNotPromoteExternalTheorem = refl

------------------------------------------------------------------------
-- 7. Compact theorem-facing boundary.
------------------------------------------------------------------------

record ContestedAmbientAuthorityBoundary : Set where
  constructor contestedAmbientAuthorityBoundary
  field
    oneCarrierPrimitiveHost : Bool
    noTypedMeetAnnihilatesSourceState : Bool
    interfaceRecognitionExhaustsSource : Bool
    externalRecognitionAloneCreatesAuthority : Bool
    coerciveDominanceCreatesLegitimateAuthority : Bool
    orderProjectionAutomaticallyDeterminesJustice : Bool
    formalSublationGuaranteesReconciliation : Bool
    sharedHyperformalCarrierCreatesExternalAuthority : Bool
    partialInterfacesAllowed : Bool
    independentlyAuthoritativeExteriorAllowed : Bool
    ambientAuthorityMustBeClaimIndexed : Bool

canonicalContestedAmbientAuthorityBoundary :
  ContestedAmbientAuthorityBoundary
canonicalContestedAmbientAuthorityBoundary =
  contestedAmbientAuthorityBoundary
    false
    false
    false
    false
    false
    false
    false
    false
    true
    true
    true

contestedAmbientAuthorityStatement : String
contestedAmbientAuthorityStatement =
  "No carrier is ambient by type declaration. Partial typed interfaces may coexist with independently authoritative exterior states; NO_TYPED_MEET and SCOPE_EXCEEDED do not annihilate source reality; recognition and coercive dominance do not self-issue authority; order/flat projections do not automatically determine situated justice; and shared 369 hyperformal geometry does not promote external authority."
