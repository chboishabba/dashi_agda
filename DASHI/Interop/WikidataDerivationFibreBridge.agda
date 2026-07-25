module DASHI.Interop.WikidataDerivationFibreBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Claim-centred derivation fibres for Wikidata/ITIR ontology work.
--
-- The base point is a surface claim or deliberately weak carrier edge.
-- A fibre contains derivations over that claim.  Ontology axes select
-- overlapping subfibres; they are not themselves fibres.  Validation is
-- computed from support/contradiction presence in the required subfibre,
-- while role/scope inapplicability is kept outside the evidential outcome.

------------------------------------------------------------------------
-- Base claims and statement context.

data StatementRole : Set where
  mainValueRole : StatementRole
  qualifierRole : StatementRole
  referenceRole : StatementRole
  candidateLinkRole : StatementRole

data ClaimKind : Set where
  wikidataStatementClaim : ClaimKind
  weakCarrierLinkClaim : ClaimKind
  externalClaimKind : String → ClaimKind

record ClaimBase : Set where
  constructor claimBase
  field
    claimId : String
    claimSurface : String
    claimKind : ClaimKind
    statementRole : StatementRole
    graphSnapshot : String

open ClaimBase public

------------------------------------------------------------------------
-- Ontology axes are structured directions of derivation.

data OntologyAxis : Set where
  bibliographicAxis : OntologyAxis
  legalAxis : OntologyAxis
  biologicalAxis : OntologyAxis
  eventOccurrentAxis : OntologyAxis
  continuantOccurrentAxis : OntologyAxis
  abstractConcreteAxis : OntologyAxis
  individualCollectiveAxis : OntologyAxis
  externalAxis : String → OntologyAxis

data AxisRequirement : Set where
  axisRequired : AxisRequirement
  axisOptional : AxisRequirement
  axisInapplicable : AxisRequirement

data Domain : Set where
  bibliographicDomain : Domain
  causalModelingDomain : Domain
  legalDomain : Domain
  biologicalDomain : Domain
  genericDomain : Domain
  externalDomain : String → Domain

record DomainPressure : Set where
  constructor domainPressure
  field
    pressureDomain : Domain
    pressuredAxis : OntologyAxis
    pressureRole : StatementRole
    axisRequirement : AxisRequirement
    pressureReason : String

open DomainPressure public

causalEffectOccurrentPressure : DomainPressure
causalEffectOccurrentPressure =
  domainPressure
    causalModelingDomain
    eventOccurrentAxis
    mainValueRole
    axisRequired
    "A causal effect main value requires an event/occurrent derivation path."

causalQualifierOccurrentPressure : DomainPressure
causalQualifierOccurrentPressure =
  domainPressure
    causalModelingDomain
    eventOccurrentAxis
    qualifierRole
    axisInapplicable
    "This validation rule is scoped to a main value rather than qualifier use."

------------------------------------------------------------------------
-- Derivations over a fixed base claim.

data DerivationPolarity : Set where
  supporting : DerivationPolarity
  contradicting : DerivationPolarity
  unresolved : DerivationPolarity

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

record Derivation (c : ClaimBase) : Set where
  constructor derivation
  field
    derivationId : String
    derivationPolarity : DerivationPolarity
    derivationAxes : List OntologyAxis
    derivationEvidence : String
    derivationProvenance : String
    derivationObligations : List String

open Derivation public

-- The total fibre over c is represented by values of Derivation c.
ClaimFibre : ClaimBase → Set
ClaimFibre c = Derivation c

-- An axis-indexed subfibre is a derivation over c plus a witness that the
-- derivation actually proceeds through the selected axis.  A derivation can
-- inhabit several subfibres because its axis list can contain several axes.
record AxisSubfibre (c : ClaimBase) (a : OntologyAxis) : Set where
  constructor axisSubfibre
  field
    subfibreDerivation : Derivation c
    usesSelectedAxis : a ∈ derivationAxes subfibreDerivation

open AxisSubfibre public

------------------------------------------------------------------------
-- Operational validation outcomes.

data FibreOutcome : Set where
  satisfied : FibreOutcome
  violated : FibreOutcome
  both : FibreOutcome
  undetermined : FibreOutcome

data ValidationOutcome : Set where
  fibreShape : FibreOutcome → ValidationOutcome
  inapplicable : String → ValidationOutcome

fibreOutcomeFromPresence : Bool → Bool → FibreOutcome
fibreOutcomeFromPresence true false = satisfied
fibreOutcomeFromPresence false true = violated
fibreOutcomeFromPresence true true = both
fibreOutcomeFromPresence false false = undetermined

validateRequiredSubfibre :
  AxisRequirement →
  Bool →
  Bool →
  ValidationOutcome
validateRequiredSubfibre axisInapplicable supportPresent contradictionPresent =
  inapplicable "The rule does not apply in this statement role or scope."
validateRequiredSubfibre axisRequired supportPresent contradictionPresent =
  fibreShape (fibreOutcomeFromPresence supportPresent contradictionPresent)
validateRequiredSubfibre axisOptional supportPresent contradictionPresent =
  fibreShape (fibreOutcomeFromPresence supportPresent contradictionPresent)

------------------------------------------------------------------------
-- Central non-collapse receipts.
--
-- Absence of a supporting path and absence of a contradicting path in a
-- required axis subfibre yields an unresolved obligation, not a violation.

missingRequiredSubfibreIsUndetermined :
  validateRequiredSubfibre axisRequired false false ≡
  fibreShape undetermined
missingRequiredSubfibreIsUndetermined = refl

contradictionWithoutSupportIsViolation :
  validateRequiredSubfibre axisRequired false true ≡
  fibreShape violated
contradictionWithoutSupportIsViolation = refl

supportAndContradictionRemainBoth :
  validateRequiredSubfibre axisRequired true true ≡
  fibreShape both
supportAndContradictionRemainBoth = refl

qualifierScopeCanBeInapplicable :
  validateRequiredSubfibre axisInapplicable false false ≡
  inapplicable "The rule does not apply in this statement role or scope."
qualifierScopeCanBeInapplicable = refl

------------------------------------------------------------------------
-- Weak links remain non-entailing carrier edges.

data LinkStrength : Set where
  weakCarrier : LinkStrength
  candidateMatch : LinkStrength
  closeAlignment : LinkStrength
  exactAlignment : LinkStrength
  identityAlignment : LinkStrength

identityTransferPermitted : LinkStrength → Bool
identityTransferPermitted weakCarrier = false
identityTransferPermitted candidateMatch = false
identityTransferPermitted closeAlignment = false
identityTransferPermitted exactAlignment = false
identityTransferPermitted identityAlignment = true

factTransferPermitted : LinkStrength → Bool
factTransferPermitted weakCarrier = false
factTransferPermitted candidateMatch = false
factTransferPermitted closeAlignment = false
factTransferPermitted exactAlignment = true
factTransferPermitted identityAlignment = true

weakCarrierDoesNotEntailIdentity :
  identityTransferPermitted weakCarrier ≡ false
weakCarrierDoesNotEntailIdentity = refl

weakCarrierBlocksFactTransfer :
  factTransferPermitted weakCarrier ≡ false
weakCarrierBlocksFactTransfer = refl
