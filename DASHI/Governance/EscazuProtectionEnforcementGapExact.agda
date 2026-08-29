module DASHI.Governance.EscazuProtectionEnforcementGapExact where

open import DASHI.Core.Prelude
import DASHI.Governance.EnvironmentalAuthoritySourceRegistryRound2Exact as Sources

------------------------------------------------------------------------
-- ESCAZU AGREEMENT: LEGAL PROTECTION INSTRUMENT != EFFECTIVE ENFORCEMENT
--
-- Article 9 requires a safe and enabling environment and appropriate,
-- effective and timely measures to prevent, investigate and punish attacks,
-- threats and intimidation against environmental human-rights defenders.
--
-- IUCN NL's 2025 synthesis of Global Witness data reports almost 1000 defenders
-- murdered or disappeared in Latin America and the Caribbean after adoption of
-- Escazu.  This is evidence of a continuing regional protection gap, not a
-- causal estimate of treaty effect and not a claim about non-parties' breach.
------------------------------------------------------------------------

data TreatyStatus : Set where
  noTreatyInstrument treatyInstrumentInForce : TreatyStatus

data EnforcementStatus : Set where
  effectiveProtection continuingLethalRisk : EnforcementStatus

record ProtectionSystemState : Set where
  constructor protectionSystemState
  field
    treaty : TreatyStatus
    enforcement : EnforcementStatus

formalProtectionWithContinuingRisk : ProtectionSystemState
formalProtectionWithContinuingRisk = protectionSystemState treatyInstrumentInForce continuingLethalRisk

treatyInstrumentDoesNotDefinitionallyEqualEffectiveProtection :
  ProtectionSystemState.enforcement formalProtectionWithContinuingRisk ≡ effectiveProtection → ⊥
treatyInstrumentDoesNotDefinitionallyEqualEffectiveProtection ()

escazuSource : Sources.SourceReference
escazuSource = Sources.escazu2018

gapSource : Sources.SourceReference
gapSource = Sources.iucnEscazuGap2025

record EscazuBoundary : Set where
  constructor escazuBoundary
  field
    treatyAdoptionEqualsImplementationSuccess : Bool
    treatyAdoptionEqualsImplementationSuccessIsFalse : treatyAdoptionEqualsImplementationSuccess ≡ false
    regionalPostAdoptionViolenceProvesTreatyCausedViolence : Bool
    regionalPostAdoptionViolenceProvesTreatyCausedViolenceIsFalse : regionalPostAdoptionViolenceProvesTreatyCausedViolence ≡ false
    nonPartyViolenceIsTreatyBreach : Bool
    nonPartyViolenceIsTreatyBreachIsFalse : nonPartyViolenceIsTreatyBreach ≡ false

canonicalEscazuBoundary : EscazuBoundary
canonicalEscazuBoundary = escazuBoundary false refl false refl false refl
