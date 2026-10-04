module DASHI.Governance.IranCubaSiegeComparativeMechanismExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Governance.IranWartimeConditionsRepressionRoutingExact as Iran
import DASHI.Governance.CubaSanctionsDomesticInstitutionMechanismExact as Cuba

------------------------------------------------------------------------
-- IRAN / CUBA SIEGE-PRESSURE COMPARISON
--
-- Comparable:
--   external pressure interacts with domestic institutions and political
--   narratives.
--
-- Not equated:
--   threat magnitude, institutional structure, repression pathway, economic
--   mechanism, historical genealogy, or causal effect size.
------------------------------------------------------------------------

data ComparativeAxis : Set where
  externalPressureAxis : ComparativeAxis
  domesticInstitutionAxis : ComparativeAxis
  blameOrSecurityNarrativeAxis : ComparativeAxis
  coerciveResponseAxis : ComparativeAxis
  infrastructureEconomicAxis : ComparativeAxis

record AxisComparison : Set where
  constructor axis-comparison
  field
    axis : ComparativeAxis
    iranReading : String
    cubaReading : String
    comparable : Bool
    comparableIsTrue : comparable ≡ true
    sameMechanism : Bool
    sameMechanismIsFalse : sameMechanism ≡ false

open AxisComparison public

externalPressureComparison : AxisComparison
externalPressureComparison =
  axis-comparison
    externalPressureAxis
    "Iran: active external military threat/war conditions plus sanctions/blockade pressure."
    "Cuba: sanctions/fuel restrictions and external economic coercion."
    true refl
    false refl

domesticInstitutionComparison : AxisComparison
domesticInstitutionComparison =
  axis-comparison
    domesticInstitutionAxis
    "Iran: pre-existing coercive institutions and wartime-security routing."
    "Cuba: domestic autocratic/economic institutions and infrastructure fragility interact with embargo costs."
    true refl
    false refl

narrativeComparison : AxisComparison
narrativeComparison =
  axis-comparison
    blameOrSecurityNarrativeAxis
    "Iran: wartime/national-security framing can route dissent into a security threat frame."
    "Cuba: sanctions can support externalisation of blame for domestic hardship."
    true refl
    false refl

record SiegeComparativeMechanism : Set where
  constructor siege-comparative-mechanism
  field
    iranMechanism : Iran.WartimeRoutingReceipt
    cubaMechanism : Cuba.CubaPressureMechanism
    axes : List AxisComparison
    crossCaseComparisonPaid : Bool
    crossCaseComparisonPaidIsTrue :
      crossCaseComparisonPaid ≡ true
    sameHistoricalMechanism : Bool
    sameHistoricalMechanismIsFalse :
      sameHistoricalMechanism ≡ false
    sameThreatMagnitude : Bool
    sameThreatMagnitudeIsFalse :
      sameThreatMagnitude ≡ false
    sameRepressionPathway : Bool
    sameRepressionPathwayIsFalse :
      sameRepressionPathway ≡ false
    universalSiegeRuleCreated : Bool
    universalSiegeRuleCreatedIsFalse :
      universalSiegeRuleCreated ≡ false

open SiegeComparativeMechanism public

canonicalComparison : SiegeComparativeMechanism
canonicalComparison =
  siege-comparative-mechanism
    Iran.canonicalWartimeRouting
    Cuba.canonicalCubaPressureMechanism
    (externalPressureComparison
    ∷ domesticInstitutionComparison
    ∷ narrativeComparison
    ∷ [])
    true refl
    false refl
    false refl
    false refl
    false refl

data ComparableAxesMeanSameMechanism : Set where
data TwoCasesCreateUniversalRule : Set where
data ExternalPressureExplainsAllDomesticOutcomes : Set where

comparableAxesDoNotCreateSameMechanism :
  ComparableAxesMeanSameMechanism → ⊥
comparableAxesDoNotCreateSameMechanism ()

twoCasesDoNotCreateUniversalRule :
  TwoCasesCreateUniversalRule → ⊥
twoCasesDoNotCreateUniversalRule ()

externalPressureDoesNotExplainEverything :
  ExternalPressureExplainsAllDomesticOutcomes → ⊥
externalPressureDoesNotExplainEverything ()
