module DASHI.Interop.WikidataDerivationFibreRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Interop.WikidataDerivationFibreBridge

------------------------------------------------------------------------
-- Canonical causal claim used by the ontology-working-group explanation.

causeClaim : ClaimBase
causeClaim =
  claimBase
    "claim:cause-001"
    "X has cause Y"
    wikidataStatementClaim
    mainValueRole
    "wikidata-snapshot:unspecified"

supportingEventDerivation : Derivation causeClaim
supportingEventDerivation =
  derivation
    "derivation:event-support"
    supporting
    (eventOccurrentAxis ∷ legalAxis ∷ [])
    "Y is reached through an event/occurrent classification path."
    "candidate ontology derivation receipt"
    []

supportingEventSubfibre : AxisSubfibre causeClaim eventOccurrentAxis
supportingEventSubfibre =
  axisSubfibre supportingEventDerivation here

supportingLegalSubfibre : AxisSubfibre causeClaim legalAxis
supportingLegalSubfibre =
  axisSubfibre supportingEventDerivation (there here)

-- One derivation can inhabit overlapping axis subfibres.
sameDerivationCanUseSeveralAxes :
  subfibreDerivation supportingEventSubfibre ≡
  subfibreDerivation supportingLegalSubfibre
sameDerivationCanUseSeveralAxes = refl

------------------------------------------------------------------------
-- Validation receipts.

supportOnlySatisfied :
  validateRequiredSubfibre axisRequired true false ≡
  fibreShape satisfied
supportOnlySatisfied = refl

contradictionOnlyViolated :
  validateRequiredSubfibre axisRequired false true ≡
  fibreShape violated
contradictionOnlyViolated = refl

supportAndContradictionBoth :
  validateRequiredSubfibre axisRequired true true ≡
  fibreShape both
supportAndContradictionBoth = refl

emptyRequiredAxisUndetermined :
  validateRequiredSubfibre axisRequired false false ≡
  fibreShape undetermined
emptyRequiredAxisUndetermined = refl

qualifierRuleInapplicable :
  validateRequiredSubfibre
    (axisRequirement causalQualifierOccurrentPressure)
    false
    false
  ≡
  inapplicable "The rule does not apply in this statement role or scope."
qualifierRuleInapplicable = refl

causalMainValueRequiresOccurrentAxis :
  axisRequirement causalEffectOccurrentPressure ≡ axisRequired
causalMainValueRequiresOccurrentAxis = refl

causalQualifierDoesNotTriggerMainValueRule :
  axisRequirement causalQualifierOccurrentPressure ≡ axisInapplicable
causalQualifierDoesNotTriggerMainValueRule = refl

weakSeeAlsoIdentityBlocked :
  identityTransferPermitted weakCarrier ≡ false
weakSeeAlsoIdentityBlocked = refl

weakSeeAlsoFactTransferBlocked :
  factTransferPermitted weakCarrier ≡ false
weakSeeAlsoFactTransferBlocked = refl
