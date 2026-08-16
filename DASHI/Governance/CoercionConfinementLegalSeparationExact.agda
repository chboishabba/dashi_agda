module DASHI.Governance.CoercionConfinementLegalSeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DependentAuthorityCoercionKernel as Coercion

------------------------------------------------------------------------
-- SOURCE CALIBRATION
--
-- Criminal Code Act 1995 (Cth), Division 270.
-- Current Australian statutory source for slavery, servitude and forced
-- labour concepts. No DOI asserted.
--
-- Evan Stark,
-- "Coercive Control: The Entrapment of Women in Personal Life",
-- Oxford University Press (2007).
-- DOI: 10.1093/oso/9780195154276.001.0001.
--
-- The statutory and social-science sources are intentionally not collapsed.
-- Shared coercion/dependency/exit-restriction mechanisms do not establish
-- identical legal classifications.
------------------------------------------------------------------------

record LegalSourceRole : Set where
  constructor legalSourceRole
  field
    authorInstitution : String
    title : String
    identifier : String
    boundedRole : String

commonwealthDivision270Source : LegalSourceRole
commonwealthDivision270Source =
  legalSourceRole
    "Commonwealth of Australia"
    "Criminal Code Act 1995, Division 270"
    "Commonwealth legislation; no DOI"
    "statutory element source for slavery, servitude and forced labour; legal application remains fact- and jurisdiction-specific"

starkCoerciveControlSource : LegalSourceRole
starkCoerciveControlSource =
  legalSourceRole
    "Evan Stark"
    "Coercive Control: The Entrapment of Women in Personal Life"
    "DOI 10.1093/oso/9780195154276.001.0001"
    "social-science construct source for coercive control and entrapment; not a statutory offence definition"

------------------------------------------------------------------------
-- Shared lower-level mechanism coordinates.
------------------------------------------------------------------------

data ControlCoordinate : Set where
  dependencyCoordinate : ControlCoordinate
  exitRestrictionCoordinate : ControlCoordinate
  sanctionCoordinate : ControlCoordinate
  authorityAsymmetryCoordinate : ControlCoordinate
  psychologicalOppressionCoordinate : ControlCoordinate
  abuseOfPowerCoordinate : ControlCoordinate
  vulnerabilityExploitationCoordinate : ControlCoordinate
  labourOrServicesCoordinate : ControlCoordinate
  ownershipLikePowerCoordinate : ControlCoordinate
  physicalConfinementCoordinate : ControlCoordinate
  territorialDisplacementCoordinate : ControlCoordinate
  epistemicClosureCoordinate : ControlCoordinate

record ControlSubstrate : Set where
  constructor controlSubstrate
  field
    coordinates : List ControlCoordinate
    authorityRelation : Coercion.AuthorityRelation

------------------------------------------------------------------------
-- Distinct classifications.  Their constructors remain separate even where
-- they consume overlapping coordinates.
------------------------------------------------------------------------

data SocialEntrapmentCandidate : Set where
  socialEntrapmentCandidate : ControlSubstrate → SocialEntrapmentCandidate

data FalseImprisonmentCandidate : Set where
  falseImprisonmentCandidate : ControlSubstrate → FalseImprisonmentCandidate

data ServitudeCandidate : Set where
  servitudeCandidate : ControlSubstrate → ServitudeCandidate

data ForcedLabourCandidate : Set where
  forcedLabourCandidate : ControlSubstrate → ForcedLabourCandidate

data SlaveryCandidate : Set where
  slaveryCandidate : ControlSubstrate → SlaveryCandidate

------------------------------------------------------------------------
-- Legal element receipts preserve the extra predicates rather than allowing
-- a generic coercion witness to manufacture a legal label.
------------------------------------------------------------------------

record ServitudeElements (substrate : ControlSubstrate) : Set where
  constructor servitudeElements
  field
    LabourOrServices : Set
    labourOrServices : LabourOrServices
    FreedomToCeaseOrLeaveSubstantiallyRestricted : Set
    freedomToCeaseOrLeaveSubstantiallyRestricted :
      FreedomToCeaseOrLeaveSubstantiallyRestricted

record ForcedLabourElements (substrate : ControlSubstrate) : Set where
  constructor forcedLabourElements
  field
    LabourOrServices : Set
    labourOrServices : LabourOrServices
    NotFreeBecauseOfCoercionThreatOrDeception : Set
    notFreeBecauseOfCoercionThreatOrDeception :
      NotFreeBecauseOfCoercionThreatOrDeception

record SlaveryElements (substrate : ControlSubstrate) : Set where
  constructor slaveryElements
  field
    PowersAttachingToOwnership : Set
    powersAttachingToOwnership : PowersAttachingToOwnership

record FalseImprisonmentElements (substrate : ControlSubstrate) : Set where
  constructor falseImprisonmentElements
  field
    CompleteRestraintWithinLegalTest : Set
    completeRestraintWithinLegalTest : CompleteRestraintWithinLegalTest
    JurisdictionSpecificAuthority : Set
    jurisdictionSpecificAuthority : JurisdictionSpecificAuthority

------------------------------------------------------------------------
-- Exact non-promotions.
------------------------------------------------------------------------

data PsychologicalCoercionEstablishesSlavery : Set where

data EntrapmentEstablishesFalseImprisonment : Set where

data ExitRestrictionEstablishesServitude : Set where

data DependencyEstablishesForcedLabour : Set where

psychologicalCoercionDoesNotEstablishSlavery :
  PsychologicalCoercionEstablishesSlavery → ⊥
psychologicalCoercionDoesNotEstablishSlavery ()

entrapmentDoesNotEstablishFalseImprisonment :
  EntrapmentEstablishesFalseImprisonment → ⊥
entrapmentDoesNotEstablishFalseImprisonment ()

exitRestrictionDoesNotEstablishServitude :
  ExitRestrictionEstablishesServitude → ⊥
exitRestrictionDoesNotEstablishServitude ()

dependencyDoesNotEstablishForcedLabour :
  DependencyEstablishesForcedLabour → ⊥
dependencyDoesNotEstablishForcedLabour ()

record CoercionConfinementLegalBoundary : Set where
  constructor coercionConfinementLegalBoundary
  field
    sharedCoercionSubstratePermitted : Bool
    socialEntrapmentEqualsFalseImprisonment : Bool
    socialEntrapmentEqualsServitude : Bool
    socialEntrapmentEqualsSlavery : Bool
    psychologicalCoercionSatisfiesOwnershipPower : Bool
    servitudeRequiresAdditionalLabourOrServicesReceipt : Bool
    slaveryRequiresOwnershipLikePowerReceipt : Bool
    falseImprisonmentRequiresJurisdictionSpecificReceipt : Bool

canonicalCoercionConfinementLegalBoundary :
  CoercionConfinementLegalBoundary
canonicalCoercionConfinementLegalBoundary =
  coercionConfinementLegalBoundary
    true false false false false true true true
