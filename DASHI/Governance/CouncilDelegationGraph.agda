module DASHI.Governance.CouncilDelegationGraph where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.SituatedConstituency as Situated

------------------------------------------------------------------------
-- Federated council graph.
--
-- Delegation and accountability are different directed edges.  Upward
-- delegation does not erase the downward recall/accountability path.
------------------------------------------------------------------------

data CouncilLevel : Set where
  neighbourhoodLevel : CouncilLevel
  localityLevel : CouncilLevel
  stateLevel : CouncilLevel
  nationalLevel : CouncilLevel

data ImmediatelyBelow : CouncilLevel → CouncilLevel → Set where
  neighbourhoodBelowLocality :
    ImmediatelyBelow neighbourhoodLevel localityLevel
  localityBelowState :
    ImmediatelyBelow localityLevel stateLevel
  stateBelowNational :
    ImmediatelyBelow stateLevel nationalLevel

record CouncilNode : Set where
  constructor councilNode
  field
    level : CouncilLevel
    constituency : Situated.SituatedConstituency
    councilLabel : String
    memberCount : Nat
    allMandatesValid : Bool
    allMandatesValidIsTrue : allMandatesValid ≡ true
    recallProcedurePresent : Bool
    recallProcedurePresentIsTrue : recallProcedurePresent ≡ true

open CouncilNode public

mkCouncilNode :
  CouncilLevel →
  Situated.SituatedConstituency →
  String →
  Nat →
  CouncilNode
mkCouncilNode councilLevel constituencyValue label count =
  councilNode
    councilLevel
    constituencyValue
    label
    count
    true
    refl
    true
    refl

data EdgeDirection : Set where
  upwardDelegationDirection : EdgeDirection
  downwardAccountabilityDirection : EdgeDirection

data CouncilEdge : CouncilLevel → CouncilLevel → Set where
  delegatesUpward :
    ∀ {lower upper} →
    ImmediatelyBelow lower upper →
    CouncilEdge lower upper

  accountsDownward :
    ∀ {lower upper} →
    ImmediatelyBelow lower upper →
    CouncilEdge upper lower

edgeDirection :
  ∀ {source target} →
  CouncilEdge source target →
  EdgeDirection
edgeDirection (delegatesUpward relation) =
  upwardDelegationDirection
edgeDirection (accountsDownward relation) =
  downwardAccountabilityDirection

neighbourhoodDelegatesToLocality :
  CouncilEdge neighbourhoodLevel localityLevel
neighbourhoodDelegatesToLocality =
  delegatesUpward neighbourhoodBelowLocality

localityAccountsToNeighbourhood :
  CouncilEdge localityLevel neighbourhoodLevel
localityAccountsToNeighbourhood =
  accountsDownward neighbourhoodBelowLocality

upwardAndDownwardEdgesRemainDistinct :
  edgeDirection neighbourhoodDelegatesToLocality
  ≡ upwardDelegationDirection
upwardAndDownwardEdgesRemainDistinct = refl

------------------------------------------------------------------------
-- Civilian supremacy as a constitutional path.
------------------------------------------------------------------------

data InstitutionKind : Set where
  peopleInstitution : InstitutionKind
  legislativeInstitution : InstitutionKind
  civilianExecutiveInstitution : InstitutionKind
  judicialInstitution : InstitutionKind
  militaryInstitution : InstitutionKind
  securityInstitution : InstitutionKind

data DirectlySubordinate : InstitutionKind → InstitutionKind → Set where
  militaryToCivilianExecutive :
    DirectlySubordinate militaryInstitution civilianExecutiveInstitution
  securityToCivilianExecutive :
    DirectlySubordinate securityInstitution civilianExecutiveInstitution
  civilianExecutiveToLegislature :
    DirectlySubordinate civilianExecutiveInstitution legislativeInstitution
  legislatureToPeople :
    DirectlySubordinate legislativeInstitution peopleInstitution

data SubordinationPath : InstitutionKind → InstitutionKind → Set where
  directSubordination :
    ∀ {lower upper} →
    DirectlySubordinate lower upper →
    SubordinationPath lower upper

  composeSubordination :
    ∀ {lower middle upper} →
    SubordinationPath lower middle →
    SubordinationPath middle upper →
    SubordinationPath lower upper

militaryToPeoplePath :
  SubordinationPath militaryInstitution peopleInstitution
militaryToPeoplePath =
  composeSubordination
    (directSubordination militaryToCivilianExecutive)
    (composeSubordination
      (directSubordination civilianExecutiveToLegislature)
      (directSubordination legislatureToPeople))

securityToPeoplePath :
  SubordinationPath securityInstitution peopleInstitution
securityToPeoplePath =
  composeSubordination
    (directSubordination securityToCivilianExecutive)
    (composeSubordination
      (directSubordination civilianExecutiveToLegislature)
      (directSubordination legislatureToPeople))

militaryAuthoritySourceIsRejected :
  Authority.AdmissibleAuthoritySource Authority.possessionOfForce →
  Authority.Never
militaryAuthoritySourceIsRejected =
  Authority.possessionOfForceRejected

record CouncilGraphBoundary : Set where
  constructor councilGraphBoundary
  field
    upwardDelegationPresent : Bool
    downwardAccountabilityPresent : Bool
    delegationAlienatesRecall : Bool
    militaryHasDirectSovereignEdge : Bool
    civilianSupremacyPathPresent : Bool
    nodeValidityCreatesPopularLegitimacy : Bool

canonicalCouncilGraphBoundary : CouncilGraphBoundary
canonicalCouncilGraphBoundary =
  councilGraphBoundary
    true
    true
    false
    false
    true
    false

canonicalCouncilDelegationGraphReceipt :
  GenericReceipt.GenericReceipt
canonicalCouncilDelegationGraphReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bidirectional council delegation graph"
    "DASHI.Governance.CouncilDelegationGraph"
    "canonicalCouncilGraphBoundary"
    "separates upward delegation from downward accountability and supplies the military-to-civilian-to-legislature-to-people subordination path"
    "real council membership, apportionment, recognition and constitutional validity remain external"
    "agda -i . DASHI/Governance/CouncilDelegationGraph.agda"
