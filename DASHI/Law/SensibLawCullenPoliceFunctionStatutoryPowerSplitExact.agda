module DASHI.Law.SensibLawCullenPoliceFunctionStatutoryPowerSplitExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Introspective correction to the Cullen duty carrier.
--
-- Rust source head before local validation:
--   a15a517388404719eca376365a148b9b28faf05f
--
-- The retained Cullen reasons support a police-function context while Edelman J
-- expressly states that the intervention was not pursuant to statutory power.
-- Therefore the historical bundled coordinate
--
--   statutoryPoliceFunction = police functions/powers
--
-- is too coarse for the live source carrier and may not be paid by observing a
-- police function alone.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustSourceHeadBeforeLocalValidation : String
rustSourceHeadBeforeLocalValidation =
  "a15a517388404719eca376365a148b9b28faf05f"

positiveOperationalActRef : String
positiveOperationalActRef = "prop:Cullen:positive-operational-act"

foreseeablePhysicalInjuryRiskRef : String
foreseeablePhysicalInjuryRiskRef =
  "prop:Cullen:foreseeable-physical-injury-risk"

policeFunctionContextRef : String
policeFunctionContextRef = "prop:Cullen:police-function-context"

statutoryPowerInvokedRef : String
statutoryPowerInvokedRef = "prop:Cullen:statutory-power-invoked"

legacyStatutoryPoliceFunctionRef : String
legacyStatutoryPoliceFunctionRef = "prop:Cullen:statutory-police-function"

record CullenPoliceFunctionStatutoryPowerSplitBoundary : Set where
  constructor cullenPoliceFunctionStatutoryPowerSplitBoundary
  field
    positiveOperationalActSourceSupported : Bool
    positiveOperationalActSourceSupportedIsTrue :
      positiveOperationalActSourceSupported ≡ true

    foreseeablePhysicalInjuryRiskSourceSupported : Bool
    foreseeablePhysicalInjuryRiskSourceSupportedIsTrue :
      foreseeablePhysicalInjuryRiskSourceSupported ≡ true

    policeFunctionContextSourceSupported : Bool
    policeFunctionContextSourceSupportedIsTrue :
      policeFunctionContextSourceSupported ≡ true

    statutoryPowerInvokedSourceSupported : Bool
    statutoryPowerInvokedSourceSupportedIsFalse :
      statutoryPowerInvokedSourceSupported ≡ false

    statutoryPowerInvocationContradictedOnEdelmanRoute : Bool
    statutoryPowerInvocationContradictedOnEdelmanRouteIsTrue :
      statutoryPowerInvocationContradictedOnEdelmanRoute ≡ true

    legacyBundledPremisePaid : Bool
    legacyBundledPremisePaidIsFalse : legacyBundledPremisePaid ≡ false

    oldDutyRuleReusableUnchanged : Bool
    oldDutyRuleReusableUnchangedIsFalse : oldDutyRuleReusableUnchanged ≡ false

    rulePremiseReconstructionRequired : Bool
    rulePremiseReconstructionRequiredIsTrue :
      rulePremiseReconstructionRequired ≡ true

    liveDutyResidualClosed : Bool
    liveDutyResidualClosedIsFalse : liveDutyResidualClosed ≡ false

    rustPremiseSplitLocallyObserved : Bool
    rustPremiseSplitLocallyObservedIsFalse :
      rustPremiseSplitLocallyObserved ≡ false

canonicalCullenPoliceFunctionStatutoryPowerSplitBoundary :
  CullenPoliceFunctionStatutoryPowerSplitBoundary
canonicalCullenPoliceFunctionStatutoryPowerSplitBoundary =
  cullenPoliceFunctionStatutoryPowerSplitBoundary
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PoliceFunctionAutomaticallyStatutoryPower : Set where
data PremiseSplitAutomaticallyDuty : Set where
data ContradictedStatutoryPowerAutomaticallyNoDuty : Set where
data PremiseAuditAutomaticallyConsumerClosure : Set where

policeFunctionDoesNotBecomeStatutoryPower :
  PoliceFunctionAutomaticallyStatutoryPower → ⊥
policeFunctionDoesNotBecomeStatutoryPower ()

premiseSplitDoesNotBecomeDuty : PremiseSplitAutomaticallyDuty → ⊥
premiseSplitDoesNotBecomeDuty ()

noStatutoryPowerDoesNotBecomeNoDuty :
  ContradictedStatutoryPowerAutomaticallyNoDuty → ⊥
noStatutoryPowerDoesNotBecomeNoDuty ()

premiseAuditDoesNotCloseConsumer :
  PremiseAuditAutomaticallyConsumerClosure → ⊥
premiseAuditDoesNotCloseConsumer ()
