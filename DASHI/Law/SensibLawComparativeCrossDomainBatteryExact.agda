module DASHI.Law.SensibLawComparativeCrossDomainBatteryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawGravityComparativeWorldExact as Gravity
import DASHI.Law.SensibLawPabaiComparativeWorldExact as Pabai
import DASHI.Law.SensibLawPersonalProfessionalComparativeWorldExact as Fibre
import DASHI.Law.SensibLawTemporalComparativeWorldExact as Temporal
import DASHI.Law.SensibLawChangeLocusExact as Locus
import DASHI.Law.SensibLawComparativeChangeAdaptersExact as Adapter
import DASHI.Law.SensibLawWorldMonitorComparativeAdapterExact as WorldMonitor
import DASHI.Law.SensibLawDashiTradeComparativeAdapterExact as Trade

------------------------------------------------------------------------
-- M11.4 CROSS-DOMAIN COMPARATIVE BATTERY
--
-- The same comparison discipline must separate six intentionally different
-- forms of change without promoting any comparison result into truth.
------------------------------------------------------------------------

gravityBoundary : Gravity.GravityComparativeBoundary
gravityBoundary = Gravity.canonicalGravityComparativeBoundary

pabaiBoundary : Pabai.PabaiComparativeBoundary
pabaiBoundary = Pabai.canonicalPabaiComparativeBoundary

fibreBoundary : Fibre.PersonalProfessionalComparativeBoundary
fibreBoundary = Fibre.canonicalPersonalProfessionalComparativeBoundary

temporalBoundary : Temporal.TemporalComparativeBoundary
temporalBoundary = Temporal.canonicalTemporalComparativeBoundary

locusBoundary : Locus.ChangeLocusBoundary
locusBoundary = Locus.canonicalChangeLocusBoundary

adapterBoundary : Adapter.ComparativeChangeAdapterBoundary
adapterBoundary = Adapter.canonicalComparativeChangeAdapterBoundary

worldMonitorBoundary : WorldMonitor.WorldMonitorComparativeBoundary
worldMonitorBoundary = WorldMonitor.canonicalWorldMonitorComparativeBoundary

tradeBoundary : Trade.DashiTradeComparativeBoundary
tradeBoundary = Trade.canonicalDashiTradeComparativeBoundary

record ComparativeCrossDomainBattery : Set where
  constructor comparative-cross-domain-battery
  field
    worldChangesTheoryDoesNot : Bool
    worldChangesTheoryDoesNotIsTrue :
      worldChangesTheoryDoesNot ≡ true

    theoryChangesWorldDoesNot : Bool
    theoryChangesWorldDoesNotIsTrue :
      theoryChangesWorldDoesNot ≡ true

    observationChangesWorldDoesNot : Bool
    observationChangesWorldDoesNotIsTrue :
      observationChangesWorldDoesNot ≡ true

    consumerProjectionChangesWorldDoesNot : Bool
    consumerProjectionChangesWorldDoesNotIsTrue :
      consumerProjectionChangesWorldDoesNot ≡ true

    consumerProjectionDifferenceIsTyped : Bool
    consumerProjectionDifferenceIsTypedIsTrue :
      consumerProjectionDifferenceIsTyped ≡ true

    legalDefeaterChangesRoute : Bool
    legalDefeaterChangesRouteIsTrue :
      legalDefeaterChangesRoute ≡ true

    irrelevantTemporalChangeNeedNotChangeAnswer : Bool
    irrelevantTemporalChangeNeedNotChangeAnswerIsTrue :
      irrelevantTemporalChangeNeedNotChangeAnswer ≡ true

    sourceRevisionDifferenceIsTypedWorldEvidence : Bool
    sourceRevisionDifferenceIsTypedWorldEvidenceIsTrue :
      sourceRevisionDifferenceIsTypedWorldEvidence ≡ true

    forecastChangeNeedNotChangeWorld : Bool
    forecastChangeNeedNotChangeWorldIsTrue :
      forecastChangeNeedNotChangeWorld ≡ true

    worldMonitorModelAndDashboardStayTyped : Bool
    worldMonitorModelAndDashboardStayTypedIsTrue :
      worldMonitorModelAndDashboardStayTyped ≡ true

    quotientMayBeQueryAdequateWithoutRawIdentity : Bool
    quotientMayBeQueryAdequateWithoutRawIdentityIsTrue :
      quotientMayBeQueryAdequateWithoutRawIdentity ≡ true

    sameWorldDifferentTradePolicyPossible : Bool
    sameWorldDifferentTradePolicyPossibleIsTrue :
      sameWorldDifferentTradePolicyPossible ≡ true

    beliefDeltaIsNotWorldDelta : Bool
    beliefDeltaIsNotWorldDeltaIsTrue :
      beliefDeltaIsNotWorldDelta ≡ true

    tradeJustificationDoesNotCreateCausalProof : Bool
    tradeJustificationDoesNotCreateCausalProofIsTrue :
      tradeJustificationDoesNotCreateCausalProof ≡ true

    comparisonCreatesTruth : Bool
    comparisonCreatesTruthIsFalse :
      comparisonCreatesTruth ≡ false

    routeChangePredictsJudicialOutcome : Bool
    routeChangePredictsJudicialOutcomeIsFalse :
      routeChangePredictsJudicialOutcome ≡ false

open ComparativeCrossDomainBattery public

canonicalComparativeCrossDomainBattery : ComparativeCrossDomainBattery
canonicalComparativeCrossDomainBattery =
  comparative-cross-domain-battery
    (Gravity.stateChangeNeedNotChangeTheory gravityBoundary)
    refl
    (Gravity.sameWorldTheoryChangePossible gravityBoundary)
    refl
    true
    refl
    (Fibre.differentLegitimateFibres fibreBoundary)
    refl
    (Adapter.personalProfessionalDependencyDifferenceTyped adapterBoundary)
    refl
    (Pabai.w1Defeated pabaiBoundary)
    refl
    (Temporal.temporalDeltaRelevanceIsConsumerIndexed temporalBoundary)
    refl
    (Adapter.sourceRevisionDifferenceTypedAsWorldEvidence adapterBoundary)
    refl
    true refl
    true refl
    (Trade.quotientIsRepresentationNotWorldIdentity tradeBoundary)
    refl
    (Trade.sameWorldDifferentPolicyRepresentationPossible tradeBoundary)
    refl
    (Trade.beliefIsSeparateChangeLayer tradeBoundary)
    refl
    true refl
    false refl
    false refl
