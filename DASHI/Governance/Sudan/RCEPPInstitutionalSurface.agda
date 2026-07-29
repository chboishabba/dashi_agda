module DASHI.Governance.Sudan.RCEPPInstitutionalSurface where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.CouncilDelegationGraph as Council
import DASHI.Governance.ExternalLegitimacyBoundary as Legitimacy
import DASHI.Governance.RelationalMandateFibre as MandateFibre
import DASHI.Governance.SituatedConstituency as Situated
import DASHI.Governance.TransitionResidual as Transition
import DASHI.Governance.Sudan.RCEPPSourceBoundary as Source

------------------------------------------------------------------------
-- RCEPP institutional interpretation surface.
--
-- Source:
--   Sudanese Resistance Committees and signatory revolutionary forces,
--   The Revolutionary Charter for Establishing People's Power,
--   11 January 2023; no DOI assigned in the supplied English edition.
--
-- The module records one disciplined reconstruction of the Charter's council,
-- recall, civilian-supremacy, public-finance, peace and transition grammar.  It
-- does not claim to be an official constitutional text or an authenticated
-- interpretation issued by Sudanese constituencies.
------------------------------------------------------------------------

data RCEPPConstituencyKind : Set where
  neighbourhoodConstituencyKind : RCEPPConstituencyKind
  ruralConstituencyKind : RCEPPConstituencyKind
  electedUnionConstituencyKind : RCEPPConstituencyKind
  idpCampConstituencyKind : RCEPPConstituencyKind
  namedConstituencyKind : String → RCEPPConstituencyKind

rceppSituatedConstituency :
  RCEPPConstituencyKind →
  Situated.SituatedConstituency
rceppSituatedConstituency neighbourhoodConstituencyKind =
  Situated.neighbourhoodConstituency
rceppSituatedConstituency ruralConstituencyKind =
  Situated.ruralConstituency
rceppSituatedConstituency idpCampConstituencyKind =
  Situated.idpCampConstituency
rceppSituatedConstituency electedUnionConstituencyKind =
  Situated.mkSituatedConstituency
    "elected trade-union constituency"
    "workplace / profession / sector"
    2023
    "elected trade union"
    (Situated.classAxis
      ∷ Situated.genderAxis
      ∷ Situated.regionAxis
      ∷ Situated.institutionalAccessAxis
      ∷ [])
    "functional constituency with elected rather than assumed representation"
rceppSituatedConstituency (namedConstituencyKind label) =
  Situated.mkSituatedConstituency
    label
    "named place"
    2023
    "named constituency institution"
    (Situated.namedGovernanceAxis label ∷ [])
    "candidate constituency pending external recognition"

canonicalRCEPPConstituencies : List Situated.SituatedConstituency
canonicalRCEPPConstituencies =
  rceppSituatedConstituency neighbourhoodConstituencyKind
  ∷ rceppSituatedConstituency ruralConstituencyKind
  ∷ rceppSituatedConstituency electedUnionConstituencyKind
  ∷ rceppSituatedConstituency idpCampConstituencyKind
  ∷ []

------------------------------------------------------------------------
-- Council graph instance.
------------------------------------------------------------------------

neighbourhoodCouncilNode : Council.CouncilNode
neighbourhoodCouncilNode =
  Council.mkCouncilNode
    Council.neighbourhoodLevel
    (rceppSituatedConstituency neighbourhoodConstituencyKind)
    "neighbourhood resistance / local council node"
    1

localityCouncilNode : Council.CouncilNode
localityCouncilNode =
  Council.mkCouncilNode
    Council.localityLevel
    (rceppSituatedConstituency ruralConstituencyKind)
    "locality legislative council node"
    1

stateCouncilNode : Council.CouncilNode
stateCouncilNode =
  Council.mkCouncilNode
    Council.stateLevel
    (rceppSituatedConstituency (namedConstituencyKind "state constituencies"))
    "state transitional legislative council node"
    1

nationalCouncilNode : Council.CouncilNode
nationalCouncilNode =
  Council.mkCouncilNode
    Council.nationalLevel
    (rceppSituatedConstituency (namedConstituencyKind "national constituencies"))
    "national transitional legislative council node"
    1

canonicalRCEPPCouncilNodes : List Council.CouncilNode
canonicalRCEPPCouncilNodes =
  neighbourhoodCouncilNode
  ∷ localityCouncilNode
  ∷ stateCouncilNode
  ∷ nationalCouncilNode
  ∷ []

canonicalNeighbourhoodToLocalityDelegation :
  Council.CouncilEdge Council.neighbourhoodLevel Council.localityLevel
canonicalNeighbourhoodToLocalityDelegation =
  Council.neighbourhoodDelegatesToLocality

canonicalLocalityToNeighbourhoodAccountability :
  Council.CouncilEdge Council.localityLevel Council.neighbourhoodLevel
canonicalLocalityToNeighbourhoodAccountability =
  Council.localityAccountsToNeighbourhood

------------------------------------------------------------------------
-- Authority and civilian supremacy.
------------------------------------------------------------------------

rceppSovereignAuthoritySource : Authority.AuthoritySource
rceppSovereignAuthoritySource =
  Authority.constituencyMandate

rceppSovereignAuthoritySourceAdmissible :
  Authority.AdmissibleAuthoritySource rceppSovereignAuthoritySource
rceppSovereignAuthoritySourceAdmissible = tt

rceppMilitaryToPeopleSubordination :
  Council.SubordinationPath
    Council.militaryInstitution
    Council.peopleInstitution
rceppMilitaryToPeopleSubordination =
  Council.militaryToPeoplePath

rceppForceAloneCannotOriginateAuthority :
  Authority.AdmissibleAuthoritySource Authority.possessionOfForce →
  Authority.Never
rceppForceAloneCannotOriginateAuthority =
  Authority.possessionOfForceRejected

record RCEPPCivilianSupremacySurface : Set where
  constructor rceppCivilianSupremacySurface
  field
    militarySubordinateToCivilianExecutive : Bool
    civilianExecutiveAccountableToLegislature : Bool
    legislatureAccountableToPeople : Bool
    militaryIndependentPoliticalMandate : Bool
    armedVetoCreatesLegitimacy : Bool
    comprehensiveRestructuringRequired : Bool

canonicalRCEPPCivilianSupremacySurface :
  RCEPPCivilianSupremacySurface
canonicalRCEPPCivilianSupremacySurface =
  rceppCivilianSupremacySurface
    true
    true
    true
    false
    false
    true

------------------------------------------------------------------------
-- Public-resource custody.
------------------------------------------------------------------------

record RCEPPPublicResourceCustody : Set where
  constructor rceppPublicResourceCustody
  field
    custodyLabel : String
    unifiedPublicTreasury : Bool
    allPublicRevenueAuditable : Bool
    militaryCommercialRevenueOffBudget : Bool
    securityCommercialRevenueOffBudget : Bool
    strategicPublicAssetsReviewable : Bool
    formalReceiptEstablishesActualAssetControl : Bool

canonicalRCEPPPublicResourceCustody :
  RCEPPPublicResourceCustody
canonicalRCEPPPublicResourceCustody =
  rceppPublicResourceCustody
    "public resources enter one civilian fiscal jurisdiction"
    true
    true
    false
    false
    true
    false

------------------------------------------------------------------------
-- Peace as reconstruction rather than an armed-elite settlement.
------------------------------------------------------------------------

record RCEPPPeaceReconstructionSurface : Set where
  constructor rceppPeaceReconstructionSurface
  field
    affectedCommunitiesParticipate : Bool
    displacedPeopleParticipate : Bool
    landClaimsAddressed : Bool
    voluntaryReturnEnabled : Bool
    reparationIncluded : Bool
    justiceIncluded : Bool
    institutionalReformIncluded : Bool
    regionalDevelopmentIncluded : Bool
    armedEliteAgreementAloneSufficient : Bool
    formalModelEstablishesPeace : Bool

canonicalRCEPPPeaceReconstructionSurface :
  RCEPPPeaceReconstructionSurface
canonicalRCEPPPeaceReconstructionSurface =
  rceppPeaceReconstructionSurface
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false

------------------------------------------------------------------------
-- Transitional state-machine instance.
------------------------------------------------------------------------

canonicalRCEPPOrganisationTransition :
  Transition.ConstitutionalPlusOne
    Transition.organiseBeforeTransfer
    Transition.canonicalCoupChart
canonicalRCEPPOrganisationTransition =
  Transition.canonicalOrganisationPlusOne

record RCEPPTransitionInvariantSurface : Set where
  constructor rceppTransitionInvariantSurface
  field
    civilianSupremacyPreserved : Bool
    equalCitizenshipPreserved : Bool
    rightsPreserved : Bool
    publicRevenueUnityPreserved : Bool
    affectedConstituenciesIncluded : Bool
    extraordinaryPowerTimeBound : Bool
    unresolvedResidualsRetained : Bool
    formalPhaseLabelCreatesAuthority : Bool

canonicalRCEPPTransitionInvariantSurface :
  RCEPPTransitionInvariantSurface
canonicalRCEPPTransitionInvariantSurface =
  rceppTransitionInvariantSurface
    true
    true
    true
    true
    true
    true
    true
    false

------------------------------------------------------------------------
-- Cross-pollination and non-promotion boundary.
------------------------------------------------------------------------

rceppMandateFibreShape :
  MandateFibre.CoarseTriadHypervoxelBridge
rceppMandateFibreShape =
  MandateFibre.canonicalCoarseTriadHypervoxelBridge

rceppLegitimacyBoundary : Legitimacy.LegitimacyBoundary
rceppLegitimacyBoundary =
  Legitimacy.canonicalLegitimacyBoundary

rceppSourceBoundary : Source.RCEPPSourceBoundary
rceppSourceBoundary =
  Source.canonicalRCEPPSourceBoundary

record RCEPPInstitutionalInterpretationBoundary : Set where
  constructor rceppInstitutionalInterpretationBoundary
  field
    sourceTextAndInterpretationSeparated : Bool
    coarseFibreAndFineRolesSeparated : Bool
    axisFreeRepresentationBlocked : Bool
    delegationAndAlienationSeparated : Bool
    upwardAndDownwardEdgesSeparated : Bool
    forceAndAuthoritySeparated : Bool
    publicCustodyAndActualAssetControlSeparated : Bool
    typedTransitionAndPopularLegitimacySeparated : Bool
    officialRCEPPInterpretationClaimed : Bool
    legalOperationClaimed : Bool

canonicalRCEPPInstitutionalInterpretationBoundary :
  RCEPPInstitutionalInterpretationBoundary
canonicalRCEPPInstitutionalInterpretationBoundary =
  rceppInstitutionalInterpretationBoundary
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false

canonicalRCEPPInstitutionalSurfaceReceipt :
  GenericReceipt.GenericReceipt
canonicalRCEPPInstitutionalSurfaceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "RCEPP institutional interpretation surface"
    "DASHI.Governance.Sudan.RCEPPInstitutionalSurface"
    "canonicalRCEPPInstitutionalInterpretationBoundary"
    "instantiates situated constituencies, bidirectional councils, civilian supremacy, unified public-resource custody, peace reconstruction and guarded constitutional transition over the generic governance spine"
    "actual representatives, apportionment, signatory recognition, legal operation, peace achievement and popular legitimacy remain external"
    "agda -i . DASHI/Governance/Sudan/RCEPPInstitutionalSurface.agda"
