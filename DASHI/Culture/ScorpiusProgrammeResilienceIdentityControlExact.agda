module DASHI.Culture.ScorpiusProgrammeResilienceIdentityControlExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SCORPIUS PROGRAMME RESILIENCE / IDENTITY CONTROL
--
-- Scorpius continued achieving production and integrated-test milestones in
-- 2025-2026. This is programme-resilience evidence only. It is not evidence of
-- departure impact for the missing Anthony Chavez unless a same-person technical
-- role is independently established.
------------------------------------------------------------------------

record ProgrammeResilienceReceipt : Set where
  constructor programme-resilience-receipt
  field
    programme : String
    evidenceWindow : String
    continuationReference : String
    productionContinued : Bool
    productionContinuedIsTrue : productionContinued ≡ true
    integrationTestingContinued : Bool
    integrationTestingContinuedIsTrue : integrationTestingContinued ≡ true
    multiInstitutionalExecution : Bool
    multiInstitutionalExecutionIsTrue : multiInstitutionalExecution ≡ true
    missingAnthonyIdentityAttached : Bool
    missingAnthonyIdentityAttachedIsFalse : missingAnthonyIdentityAttached ≡ false
    boundedReading : String

scorpiusResilience : ProgrammeResilienceReceipt
scorpiusResilience = programme-resilience-receipt
  "Scorpius accelerator"
  "2025-2026"
  "LLNL 2025 first production LRU delivery; LLNL 2026 milestone shipments / Integrated Test Stand"
  true refl
  true refl
  true refl
  false refl
  "Scorpius production, vendor qualification and integrated testing continued across a multi-lab programme. This may serve as a programme-resilience control, but cannot be attributed as post-loss continuity for the missing Anthony Chavez because the DARHT/Scorpius engineer identity is Mark Anthony Chavez and the same-person weld is not owned."

record ScorpiusIdentityControlBoundary : Set where
  constructor scorpius-identity-control-boundary
  field
    programmeContinuityImpliesSpecificPersonWasReplaceable : Bool
    programmeContinuityImpliesSpecificPersonWasReplaceableIsFalse :
      programmeContinuityImpliesSpecificPersonWasReplaceable ≡ false
    sameInstitutionAndNameImpliesIdentity : Bool
    sameInstitutionAndNameImpliesIdentityIsFalse :
      sameInstitutionAndNameImpliesIdentity ≡ false
    programmeResilienceCanBeUsedAsGenericMatchedControl : Bool
    programmeResilienceCanBeUsedAsGenericMatchedControlIsTrue :
      programmeResilienceCanBeUsedAsGenericMatchedControl ≡ true

canonicalScorpiusIdentityControlBoundary : ScorpiusIdentityControlBoundary
canonicalScorpiusIdentityControlBoundary = scorpius-identity-control-boundary
  false refl
  false refl
  true refl
