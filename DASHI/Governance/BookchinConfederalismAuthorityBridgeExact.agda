module DASHI.Governance.BookchinConfederalismAuthorityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.CouncilDelegationGraph as Council
import DASHI.Governance.LocalGlobalCouncilGluing as Gluing

------------------------------------------------------------------------
-- PRIMARY SOURCE: Murray Bookchin, "The Meaning of Confederalism".
--
-- Provenance class: PRIMARY SOURCE for the statements in the source boundary;
-- DASHI-DERIVED for the adapter into existing mandate/council/gluing owners.
-- The adapter is not attributed to Bookchin.
------------------------------------------------------------------------

record BookchinConfederalismSourceBoundary : Set where
  constructor bookchinConfederalismSourceBoundary
  field
    sourceAuthor : String
    sourceTitle : String
    sourceURL : String

    faceToFacePopularAssemblies : Bool
    localAssembliesFormulatePolicy : Bool
    confederalDelegatesMandatedRecallable : Bool
    delegatesResponsibleToSelectingAssemblies : Bool
    confederalCouncilsCoordinateAndAdminister : Bool
    councilsAreNotSourcePolicyMakingBody : Bool
    policyAndAdministrationDistinguished : Bool
    bottomUpPowerFlowDescribed : Bool
    intercommunityInterdependenceDescribed : Bool

open BookchinConfederalismSourceBoundary public

canonicalBookchinConfederalismSourceBoundary : BookchinConfederalismSourceBoundary
canonicalBookchinConfederalismSourceBoundary =
  bookchinConfederalismSourceBoundary
    "Murray Bookchin"
    "The Meaning of Confederalism"
    "https://theanarchistlibrary.org/library/murray-bookchin-the-meaning-of-confederalism"
    true
    true
    true
    true
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- DASHI bridge.
--
-- Existing repo machinery is reused because it already distinguishes scoped,
-- recallable authority, upward delegation/downward accountability, and
-- compatibility-gated local/global gluing.  This is a structural alignment,
-- not a claim that Bookchin authored these Agda types or that an actual polity
-- satisfies either model.
------------------------------------------------------------------------

record BookchinDASHIAlignment : Set where
  constructor bookchinDASHIAlignment
  field
    mandateBoundary : Authority.MandateAuthorityBoundary
    councilBoundary : Council.CouncilGraphBoundary
    gluingBoundary : Gluing.CouncilGluingBoundary

    sourceRecallAlignsWithNonAlienatingMandatePattern : Bool
    sourceCoordinationAlignsWithCouncilLayerPattern : Bool
    sourceBottomUpStructureAlignsWithLocalGlobalGluingPattern : Bool

open BookchinDASHIAlignment public

canonicalBookchinDASHIAlignment : BookchinDASHIAlignment
canonicalBookchinDASHIAlignment =
  bookchinDASHIAlignment
    Authority.canonicalMandateAuthorityBoundary
    Council.canonicalCouncilGraphBoundary
    Gluing.canonicalCouncilGluingBoundary
    true
    true
    true

bookchinBridgePreservesDelegationAccountabilityDistinction :
  Council.edgeDirection Council.neighbourhoodDelegatesToLocality
  ≡ Council.upwardDelegationDirection
bookchinBridgePreservesDelegationAccountabilityDistinction =
  Council.upwardAndDownwardEdgesRemainDistinct

record BookchinConfederalismBridgeBoundary : Set where
  constructor bookchinConfederalismBridgeBoundary
  field
    sourceModelCreatesActualPoliticalLegitimacy : Bool
    sourceModelCreatesActualConstituencyMandate : Bool
    sourceModelEqualsCanonicalDASHICouncilGraph : Bool
    dashiBridgeAttributedToBookchin : Bool
    policyAdministrationDistinctionRetained : Bool
    recallabilityRetained : Bool
    localGlobalCompatibilityStillRequired : Bool

open BookchinConfederalismBridgeBoundary public

canonicalBookchinConfederalismBridgeBoundary : BookchinConfederalismBridgeBoundary
canonicalBookchinConfederalismBridgeBoundary =
  bookchinConfederalismBridgeBoundary
    false
    false
    false
    false
    true
    true
    true

canonicalBookchinConfederalismBridgeReceipt : GenericReceipt.GenericReceipt
canonicalBookchinConfederalismBridgeReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Bookchin confederalism / DASHI scoped-authority bridge"
    "DASHI.Governance.BookchinConfederalismAuthorityBridgeExact"
    "canonicalBookchinDASHIAlignment"
    "records Bookchin's source distinction between local assembly policy-making and mandated/recallable confederal coordination, then aligns that shape with existing DASHI mandate, council-edge and compatibility-gated gluing machinery"
    "the source does not instantiate an actual legitimate polity; the Agda bridge is DASHI-derived and is not attributed to Bookchin"
    "agda -i . DASHI/Governance/BookchinConfederalismAuthorityBridgeRegression.agda"
