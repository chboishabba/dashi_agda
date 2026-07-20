module DASHI.Promotion.SystemicDistressReframingBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Promotion.DerivedGovernanceAdmissibility as Governance
import DASHI.Biology.BraidedEmotionOperationalSemantics as Emotion

------------------------------------------------------------------------
-- Distress may be read in personal, relational, or systemic context without
-- pretending that one interpretive frame replaces clinical assessment.

data SignalContext : Set where
  personalContext relationalContext systemicContext mixedContext unknownContext : SignalContext

data DistressUse : Set where
  selfDescriptionUse contextualHypothesisUse systemicCritiqueUse diagnosticUse causalClosureUse treatmentDirectionUse : DistressUse

record DistressSignal : Set where
  constructor distressSignal
  field
    signalLabel : String
    context : SignalContext
    firstPersonAuthority : Bool
    observedImpact : String

open DistressSignal public

canonicalDistressSignal : DistressSignal
canonicalDistressSignal =
  distressSignal
    "experienced distress treated as protected first-person evidence"
    mixedContext
    true
    "may motivate personal, relational, and systemic inquiry without fixing one cause"

data Never : Set where

data AdmissibleDistressUse : DistressUse → Set where
  selfDescriptionAdmissible : AdmissibleDistressUse selfDescriptionUse
  contextualHypothesisAdmissible : AdmissibleDistressUse contextualHypothesisUse
  systemicCritiqueAdmissible : AdmissibleDistressUse systemicCritiqueUse

diagnosisNotDerivedFromReframing : AdmissibleDistressUse diagnosticUse → Never
diagnosisNotDerivedFromReframing ()

causalClosureNotDerivedFromReframing : AdmissibleDistressUse causalClosureUse → Never
causalClosureNotDerivedFromReframing ()

treatmentNotDerivedFromReframing : AdmissibleDistressUse treatmentDirectionUse → Never
treatmentNotDerivedFromReframing ()

------------------------------------------------------------------------
-- The "10% power-up" is encoded as a chart-expansion metaphor, not as a
-- measured treatment effect or proof that every diagnosis is systemic error.

record TenPercentPowerUp : Set where
  constructor tenPercentPowerUp
  field
    baselineChartLabel : String
    expandedChartLabel : String
    addedPerspectiveAxes : Nat
    preservesFirstPersonSignal : Bool
    permitsSystemicHypothesis : Bool
    guaranteesSymptomRelief : Bool
    guaranteesSymptomReliefIsFalse : guaranteesSymptomRelief ≡ false
    replacesClinicalCare : Bool
    replacesClinicalCareIsFalse : replacesClinicalCare ≡ false
    interpretation : String

canonicalTenPercentPowerUp : TenPercentPowerUp
canonicalTenPercentPowerUp =
  tenPercentPowerUp
    "1.0 binary/self-only chart"
    "1.1 expanded personal-relational-systemic chart"
    1
    true
    true
    false refl
    false refl
    "zooming out may reframe distress as context-bearing data; numeric efficacy, diagnosis reversal, and treatment authority are not claimed"

record ProtectedSignalUse : Set where
  constructor protectedSignalUse
  field
    signal : DistressSignal
    use : DistressUse
    consentRetained : Bool
    uncertaintyRetained : Bool
    dignityRetained : Bool
    interpretation : String

sacredDataAsProtectedUse : ProtectedSignalUse
sacredDataAsProtectedUse =
  protectedSignalUse
    canonicalDistressSignal
    systemicCritiqueUse
    true
    true
    true
    "sacred data means protected, dignified, context-bearing testimony; it does not mean infallible measurement or automatic causal proof"

------------------------------------------------------------------------
-- Reuse repository governance rather than opening a new diagnostic island.

safeProxyInterpretation :
  Governance.AdmissibleInterpretation
    Governance.processedProxy
    Governance.proxyInterpretation
safeProxyInterpretation = Governance.safeProxyWitness

emotionOperationalSurface : Set
emotionOperationalSurface = Emotion.OperationalState

record SystemicDistressBoundary : Set where
  constructor systemicDistressBoundary
  field
    systemicContextMayBeConsidered : Bool
    personalAndBiologicalFactorsMayBeConsidered : Bool
    everyDiagnosisReducedToCapitalism : Bool
    everyDiagnosisReducedToCapitalismIsFalse :
      everyDiagnosisReducedToCapitalism ≡ false
    distressIsAutomaticTruth : Bool
    distressIsAutomaticTruthIsFalse : distressIsAutomaticTruth ≡ false
    diagnosisAuthorityPromoted : Bool
    diagnosisAuthorityPromotedIsFalse : diagnosisAuthorityPromoted ≡ false
    interventionAuthorityPromoted : Bool
    interventionAuthorityPromotedIsFalse : interventionAuthorityPromoted ≡ false
    interpretation : String

canonicalSystemicDistressBoundary : SystemicDistressBoundary
canonicalSystemicDistressBoundary =
  systemicDistressBoundary
    true
    true
    false refl
    false refl
    false refl
    false refl
    "distress can carry systemic diagnostic value in the ordinary descriptive sense while clinical diagnosis, causal closure, and treatment remain evidence-gated"
