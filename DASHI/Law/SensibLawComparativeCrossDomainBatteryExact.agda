module DASHI.Law.SensibLawComparativeCrossDomainBatteryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawGravityComparativeWorldExact as Gravity
import DASHI.Law.SensibLawPabaiComparativeWorldExact as Pabai
import DASHI.Law.SensibLawPersonalProfessionalComparativeWorldExact as Fibre
import DASHI.Law.SensibLawTemporalComparativeWorldExact as Temporal
import DASHI.Law.SensibLawChangeLocusExact as Locus

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

    legalDefeaterChangesRoute : Bool
    legalDefeaterChangesRouteIsTrue :
      legalDefeaterChangesRoute ≡ true

    irrelevantTemporalChangeNeedNotChangeAnswer : Bool
    irrelevantTemporalChangeNeedNotChangeAnswerIsTrue :
      irrelevantTemporalChangeNeedNotChangeAnswer ≡ true

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
    (Gravity.stateMayChangeWhileRegularityInvariant gravityBoundary)
    refl
    (Gravity.sameWorldTheoryChangePossible gravityBoundary)
    refl
    (Locus.observationDeltaEqualsWorldDelta locusBoundary == false)
    refl
    (Fibre.differentLegitimateFibres fibreBoundary)
    refl
    (Pabai.w1Defeated pabaiBoundary)
    refl
    (Temporal.temporalDeltaRelevanceIsConsumerIndexed temporalBoundary)
    refl
    false refl
    false refl
