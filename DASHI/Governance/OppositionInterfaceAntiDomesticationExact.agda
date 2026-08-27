module DASHI.Governance.OppositionInterfaceAntiDomesticationExact where

------------------------------------------------------------------------
-- OPPOSITION INTERFACE / ANTI-DOMESTICATION
--
-- Structural formalisation of the pattern shared by sanctioned protest,
-- regulated collective bargaining, consultative student representation and
-- bounded electoral competition: real opposition inside an institutionally
-- admissible interface does not by itself prove that opposition can alter the
-- rule that determines admissibility.  The named domains are illustrative
-- carrier labels only; no theorem asserts that a live institution instantiates
-- the closed configuration.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Governance.ContestedAmbientAuthorityHyperformalismExact as Ambient
import DASHI.Governance.ExternalLegitimacyBoundary as External
import DASHI.Governance.OptionConeCoercionExact as OptionCone

------------------------------------------------------------------------
-- 1. Admissible-antithesis fibre.
------------------------------------------------------------------------

data OppositionDomain : Set where
  protestDomain labourDomain studentRepresentationDomain electoralDomain :
    OppositionDomain

data OppositionState : Set where
  recognisedOpposition exteriorOpposition : OppositionState

data AdministrativeState : Set where
  admittedAdministrativeObject : AdministrativeState

data OppositionMeet : Set where
  recognisedMeet : OppositionMeet

oppositionCarrier : Ambient.NormativeCarrier
oppositionCarrier = Ambient.normativeCarrier OppositionState "opposition carrier"

administrativeCarrier : Ambient.NormativeCarrier
administrativeCarrier =
  Ambient.normativeCarrier AdministrativeState "administrative admission carrier"

oppositionAdministrativeInterface :
  Ambient.TypedInterface oppositionCarrier administrativeCarrier
oppositionAdministrativeInterface =
  Ambient.typedInterface
    OppositionMeet
    (λ { recognisedMeet → recognisedOpposition })
    (λ { recognisedMeet → admittedAdministrativeObject })

oppositionExteriorWitness :
  Ambient.ExteriorWitness oppositionAdministrativeInterface
oppositionExteriorWitness =
  Ambient.exteriorWitness exteriorOpposition (λ { recognisedMeet () })

------------------------------------------------------------------------
-- 2. Admission can preserve opposition while withholding power over the
--    admission rule itself.
------------------------------------------------------------------------

data AdmissionRule : Set where
  currentAdmissionRule revisedAdmissionRule : AdmissionRule

data RuleChangeAuthority : OppositionState → Set where
  recognisedCannotSelfIssueRuleChange :
    RuleChangeAuthority recognisedOpposition → RuleChangeAuthority recognisedOpposition

-- Empty-by-elimination capability for the canonical recognised opposition.
-- We keep a separate predicate so ordinary opposition and meta-rule authority
-- cannot be silently identified.
data CanAlterAdmissionRule : OppositionState → Set where

recognisedOppositionCannotAutomaticallyAlterRule :
  CanAlterAdmissionRule recognisedOpposition → ⊥
recognisedOppositionCannotAutomaticallyAlterRule ()

record AdmissibleOppositionFibre : Set where
  constructor admissibleOppositionFibre
  field
    domain : OppositionDomain
    admittedState : OppositionState
    meetWitness : OppositionMeet
    admittedStateFromMeet :
      Ambient.left oppositionAdministrativeInterface meetWitness ≡ admittedState

open AdmissibleOppositionFibre public

canonicalAdmissibleOpposition : OppositionDomain → AdmissibleOppositionFibre
canonicalAdmissibleOpposition domain =
  admissibleOppositionFibre domain recognisedOpposition recognisedMeet refl

record BoundedOppositionWitness : Set where
  constructor boundedOppositionWitness
  field
    oppositionExists : AdmissibleOppositionFibre
    ruleChangeNotManufactured :
      CanAlterAdmissionRule (admittedState oppositionExists) → ⊥

canonicalBoundedOpposition : OppositionDomain → BoundedOppositionWitness
canonicalBoundedOpposition domain =
  boundedOppositionWitness
    (canonicalAdmissibleOpposition domain)
    recognisedOppositionCannotAutomaticallyAlterRule

------------------------------------------------------------------------
-- 3. Plurality of admitted positions != openness of the admission algebra.
------------------------------------------------------------------------

data Position : Set where
  positionA positionB : Position

sameAdmissionRule : Position → AdmissionRule
sameAdmissionRule _ = currentAdmissionRule

visibleOpposition : positionA ≡ positionB → ⊥
visibleOpposition ()

bothPositionsShareAdmissionRule :
  sameAdmissionRule positionA ≡ sameAdmissionRule positionB
bothPositionsShareAdmissionRule = refl

record VisiblePluralitySharedSkeleton : Set where
  constructor visiblePluralitySharedSkeleton
  field
    first second : Position
    positionsDistinct : first ≡ second → ⊥
    admissionRuleSame : sameAdmissionRule first ≡ sameAdmissionRule second

canonicalVisiblePluralitySharedSkeleton : VisiblePluralitySharedSkeleton
canonicalVisiblePluralitySharedSkeleton =
  visiblePluralitySharedSkeleton positionA positionB (λ ()) refl

------------------------------------------------------------------------
-- 4. Recognition must not consume the exterior.
------------------------------------------------------------------------

oppositionInterfaceIsNotExhaustive :
  Ambient.LeftExhaustive oppositionAdministrativeInterface → ⊥
oppositionInterfaceIsNotExhaustive exhaustive =
  Ambient.ExteriorWitness.notRepresented oppositionExteriorWitness
    (Ambient.LeftExhaustive.represent exhaustive exteriorOpposition)
    (Ambient.LeftExhaustive.representExact exhaustive exteriorOpposition)

record AntiDomesticationRequirement : Set where
  constructor antiDomesticationRequirement
  field
    exteriorRemainsPossible : Ambient.ExteriorWitness oppositionAdministrativeInterface
    admittedOppositionDoesNotOwnWholeSource :
      Ambient.LeftExhaustive oppositionAdministrativeInterface → ⊥
    ruleChangeAuthoritySeparatelyTyped :
      CanAlterAdmissionRule recognisedOpposition → ⊥

canonicalAntiDomesticationRequirement : AntiDomesticationRequirement
canonicalAntiDomesticationRequirement =
  antiDomesticationRequirement
    oppositionExteriorWitness
    oppositionInterfaceIsNotExhaustive
    recognisedOppositionCannotAutomaticallyAlterRule

------------------------------------------------------------------------
-- 5. A sanctioned/administratively legible route may preserve some options
--    while a coercive route contracts others; existing option-cone mathematics
--    remains the theorem owner for that dynamic claim.
------------------------------------------------------------------------

canonicalReachabilityContractionStillRequiresLostOptionWitness :
  OptionCone.StrictSafeReachabilityContraction
    OptionCone.demoReachability
    OptionCone.beforeResponse
    OptionCone.coerciveOutcome
canonicalReachabilityContractionStillRequiresLostOptionWitness =
  OptionCone.canonicalCoerciveReachabilityContraction

------------------------------------------------------------------------
-- 6. Local formalisation never manufactures real popular/legal legitimacy.
------------------------------------------------------------------------

formalModelStillDoesNotCreatePopularLegitimacy :
  External.sourceCreatesPopularLegitimacy
    (External.formalReceiptLegitimacySource External.localTypecheckingReceipt)
  ≡ false
formalModelStillDoesNotCreatePopularLegitimacy =
  External.formalReceiptDoesNotCreatePopularLegitimacy External.localTypecheckingReceipt

------------------------------------------------------------------------
-- 7. Boundary.
------------------------------------------------------------------------

record OppositionInterfaceAntiDomesticationBoundary : Set where
  constructor oppositionInterfaceAntiDomesticationBoundary
  field
    admittedOppositionImpliesRuleChangePower : Bool
    administrativeLegibilityExhaustsPoliticalCarrier : Bool
    visibleTwoPositionCompetitionImpliesOpenCarrier : Bool
    nonAdmissionImpliesNoOppositionState : Bool
    formalModelCreatesPopularLegitimacy : Bool
    admittedOppositionMayBeReal : Bool
    exteriorOppositionMayRemainReal : Bool
    antiDomesticationRequiresSeparateMetaRuleAuthority : Bool

canonicalOppositionInterfaceAntiDomesticationBoundary :
  OppositionInterfaceAntiDomesticationBoundary
canonicalOppositionInterfaceAntiDomesticationBoundary =
  oppositionInterfaceAntiDomesticationBoundary
    false false false false false true true true

oppositionInterfaceAntiDomesticationStatement : String
oppositionInterfaceAntiDomesticationStatement =
  "An institution can preserve real, visible opposition inside an admissible interface while retaining control of the rule that defines admissibility. Recognition therefore does not prove co-sovereignty or meta-rule power, and plurality inside one admission algebra does not prove openness of the ambient carrier. Anti-domestication requires the exterior and its provenance to remain positively representable as exterior rather than being converted into nonexistence."
