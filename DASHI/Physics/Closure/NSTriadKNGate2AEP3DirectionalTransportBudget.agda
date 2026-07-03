module DASHI.Physics.Closure.NSTriadKNGate2AEP3DirectionalTransportBudget where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import DASHI.Physics.Closure.NSTriadKNGate2ASampledComparisonEnvelope
  using ( NSTriadKNGate2ASampledComparisonEnvelope
        ; canonicalNSTriadKNGate2ASampledComparisonEnvelope
        )
import DASHI.Physics.Closure.NSTriadKNGate2ASampledComparisonEnvelope
  as Envelope
open import DASHI.Physics.Closure.NSTriadKNGate2AConeRestrictedDefectBudget using
  ( NSTriadKNGate2AConeRestrictedDefectBudget
  ; canonicalNSTriadKNGate2AConeRestrictedDefectBudget
  )
open import DASHI.Physics.Closure.NSTriadKNGate2AQuotientAwareLiftDefectExpansion using
  ( NSTriadKNGate2AQuotientAwareLiftDefectExpansion
  ; canonicalNSTriadKNGate2AQuotientAwareLiftDefectExpansion
  )

------------------------------------------------------------------------
-- EP3: directional transport budget.
--
-- This is the concrete analytic replacement for the dead coarse route
--
--   rho_transfer <= (C_neg^+ / c_abs^-) rho_N.
--
-- The budget keeps numerator and denominator transport directional and
-- cone-restricted. This is the exact theorem shape now supported by the
-- live sprint notes.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadKNGate2AEP3Status : Set where
  coarseWorstCaseRouteRejected :
    NSTriadKNGate2AEP3Status
  directionalBudgetFactorizationRecorded :
    NSTriadKNGate2AEP3Status
  sampledDirectionalLedgerRecorded :
    NSTriadKNGate2AEP3Status
  conservativeQuarterTargetRecorded :
    NSTriadKNGate2AEP3Status
  quotientAwareTransportRouteRecorded :
    NSTriadKNGate2AEP3Status
  noNSOrClayPromotion :
    NSTriadKNGate2AEP3Status

canonicalEP3Statuses : List NSTriadKNGate2AEP3Status
canonicalEP3Statuses =
  coarseWorstCaseRouteRejected
  ∷ directionalBudgetFactorizationRecorded
  ∷ sampledDirectionalLedgerRecorded
  ∷ conservativeQuarterTargetRecorded
  ∷ quotientAwareTransportRouteRecorded
  ∷ noNSOrClayPromotion
  ∷ []

data NSTriadKNGate2AEP3BudgetTerm : Set where
  seamRayleighRatioTerm :
    NSTriadKNGate2AEP3BudgetTerm
  directionalNumeratorTransportTerm :
    NSTriadKNGate2AEP3BudgetTerm
  directionalDenominatorTransportTerm :
    NSTriadKNGate2AEP3BudgetTerm
  transportedLeakageRatioTerm :
    NSTriadKNGate2AEP3BudgetTerm
  finalMarginClosingTerm :
    NSTriadKNGate2AEP3BudgetTerm

canonicalEP3BudgetTerms : List NSTriadKNGate2AEP3BudgetTerm
canonicalEP3BudgetTerms =
  seamRayleighRatioTerm
  ∷ directionalNumeratorTransportTerm
  ∷ directionalDenominatorTransportTerm
  ∷ transportedLeakageRatioTerm
  ∷ finalMarginClosingTerm
  ∷ []

data NSTriadKNGate2AEP3SampledShell : Set where
  shell6DirectionalLedger :
    NSTriadKNGate2AEP3SampledShell
  shell8DirectionalLedger :
    NSTriadKNGate2AEP3SampledShell
  shell10DirectionalLedger :
    NSTriadKNGate2AEP3SampledShell

canonicalEP3SampledShells : List NSTriadKNGate2AEP3SampledShell
canonicalEP3SampledShells =
  shell6DirectionalLedger
  ∷ shell8DirectionalLedger
  ∷ shell10DirectionalLedger
  ∷ []

canonicalBudgetFactorizationText : String
canonicalBudgetFactorizationText =
  "For x in E_N(epsilon), if <J_N x, L_neg J_N x> <= C_neg^dir(x) * x^T L_bad x and <J_N x, L_abs J_N x> >= c_abs^dir(x) * x^T L_good x, then the transported leakage ratio is bounded by (C_neg^dir(x) / c_abs^dir(x)) * (x^T L_bad x / x^T L_good x)."

canonicalRouteSelectionText : String
canonicalRouteSelectionText =
  "The blunt worst-case quotient route is ruled out on N=6,8,10 because the induced upper bounds land around 17.7, 17.7, and 20.5. The live route is therefore directional: extremizer-aware, quotient-aware, and cone-restricted."

canonicalObservedLedgerText : String
canonicalObservedLedgerText =
  "Observed directional transported ratios on the sampled extremizer family are theta_6 ~= 0.1681546, theta_8 ~= 0.1677930, theta_10 ~= 0.1678154, all well below the conservative target 1/4 and far below 1."

canonicalImprovementText : String
canonicalImprovementText =
  "Improvement over the dead coarse route: about 105.65x on N=6, 105.72x on N=8, and 122.11x on N=10."

canonicalClosingText : String
canonicalClosingText =
  "EP3 reduces Gate 2-A to a directional budget problem: control the quotient C_neg^dir / c_abs^dir on the near-extremizer cone, then combine it with the Gate 1 seam ratio without losing the strict margin below 1."

canonicalQuotientAwareText : String
canonicalQuotientAwareText =
  "Quotient-aware refinement: compare J_N^neg to the common reference lift J_N^abs via the defect DeltaJ = J_N^neg - J_N^abs, and bound the principal, cross, and pure-defect pieces separately on the near-extremizer cone instead of collapsing everything into one worst-case quotient."

canonicalDefectBudgetConsumptionText : String
canonicalDefectBudgetConsumptionText =
  "EP3 now consumes the quotient-aware defect expansion directly: principal reference transport supplies the leading directional term, while the cross-defect and pure-defect corrections must fit inside a subcritical eta_defect budget on E_N(epsilon)."

toEnvelopeShell : NSTriadKNGate2AEP3SampledShell → Envelope.SampledShell
toEnvelopeShell shell6DirectionalLedger = Envelope.shell6
toEnvelopeShell shell8DirectionalLedger = Envelope.shell8
toEnvelopeShell shell10DirectionalLedger = Envelope.shell10

ep3SampledCoarseEnvelopeRejected :
  (s : NSTriadKNGate2AEP3SampledShell) →
  Envelope.coarseEnvelopeRouteCloses (toEnvelopeShell s) ≡ false
ep3SampledCoarseEnvelopeRejected shell6DirectionalLedger =
  Envelope.sampledCoarseEnvelopeRouteRejected Envelope.shell6
ep3SampledCoarseEnvelopeRejected shell8DirectionalLedger =
  Envelope.sampledCoarseEnvelopeRouteRejected Envelope.shell8
ep3SampledCoarseEnvelopeRejected shell10DirectionalLedger =
  Envelope.sampledCoarseEnvelopeRouteRejected Envelope.shell10

ep3SampledDirectionalBelowQuarter :
  (s : NSTriadKNGate2AEP3SampledShell) →
  Envelope.directionalRouteBelowQuarter (toEnvelopeShell s) ≡ true
ep3SampledDirectionalBelowQuarter shell6DirectionalLedger =
  Envelope.sampledDirectionalRouteBelowQuarter Envelope.shell6
ep3SampledDirectionalBelowQuarter shell8DirectionalLedger =
  Envelope.sampledDirectionalRouteBelowQuarter Envelope.shell8
ep3SampledDirectionalBelowQuarter shell10DirectionalLedger =
  Envelope.sampledDirectionalRouteBelowQuarter Envelope.shell10

record NSTriadKNGate2AEP3DirectionalTransportBudget : Setω where
  constructor mkNSTriadKNGate2AEP3DirectionalTransportBudget
  field
    statuses : List NSTriadKNGate2AEP3Status
    statusesAreCanonical :
      statuses ≡ canonicalEP3Statuses

    budgetTerms : List NSTriadKNGate2AEP3BudgetTerm
    budgetTermsAreCanonical :
      budgetTerms ≡ canonicalEP3BudgetTerms

    sampledShells : List NSTriadKNGate2AEP3SampledShell
    sampledShellsAreCanonical :
      sampledShells ≡ canonicalEP3SampledShells

    budgetFactorizationText : String
    budgetFactorizationTextIsCanonical :
      budgetFactorizationText ≡ canonicalBudgetFactorizationText

    routeSelectionText : String
    routeSelectionTextIsCanonical :
      routeSelectionText ≡ canonicalRouteSelectionText

    observedLedgerText : String
    observedLedgerTextIsCanonical :
      observedLedgerText ≡ canonicalObservedLedgerText

    improvementText : String
    improvementTextIsCanonical :
      improvementText ≡ canonicalImprovementText

    closingText : String
    closingTextIsCanonical :
      closingText ≡ canonicalClosingText

    quotientAwareText : String
    quotientAwareTextIsCanonical :
      quotientAwareText ≡ canonicalQuotientAwareText

    quotientAwareDefectExpansion :
      NSTriadKNGate2AQuotientAwareLiftDefectExpansion
    quotientAwareDefectExpansionIsCanonical :
      quotientAwareDefectExpansion
        ≡ canonicalNSTriadKNGate2AQuotientAwareLiftDefectExpansion

    sampledComparisonEnvelope :
      NSTriadKNGate2ASampledComparisonEnvelope
    sampledComparisonEnvelopeIsCanonical :
      sampledComparisonEnvelope
        ≡ canonicalNSTriadKNGate2ASampledComparisonEnvelope

    coneRestrictedDefectBudget :
      NSTriadKNGate2AConeRestrictedDefectBudget
    coneRestrictedDefectBudgetIsCanonical :
      coneRestrictedDefectBudget
        ≡ canonicalNSTriadKNGate2AConeRestrictedDefectBudget

    defectBudgetConsumptionText : String
    defectBudgetConsumptionTextIsCanonical :
      defectBudgetConsumptionText ≡ canonicalDefectBudgetConsumptionText

    budgetTermCount : Nat
    budgetTermCountIs5 :
      budgetTermCount ≡ 5

    sampledShellCount : Nat
    sampledShellCountIs3 :
      sampledShellCount ≡ 3

    sampledCoarseEnvelopeRejectedProof :
      (s : NSTriadKNGate2AEP3SampledShell) →
      Envelope.coarseEnvelopeRouteCloses (toEnvelopeShell s) ≡ false

    sampledDirectionalBelowQuarterProof :
      (s : NSTriadKNGate2AEP3SampledShell) →
      Envelope.directionalRouteBelowQuarter (toEnvelopeShell s) ≡ true

    ep3CoarseWorstCaseRouteRejected : Bool
    ep3CoarseWorstCaseRouteRejectedIsTrue :
      ep3CoarseWorstCaseRouteRejected ≡ true

    ep3DirectionalBudgetFactorizationInstalled : Bool
    ep3DirectionalBudgetFactorizationInstalledIsTrue :
      ep3DirectionalBudgetFactorizationInstalled ≡ true

    ep3SampledDirectionalLedgerRecorded : Bool
    ep3SampledDirectionalLedgerRecordedIsTrue :
      ep3SampledDirectionalLedgerRecorded ≡ true

    ep3DirectionalRatioApproxOneSixthObserved : Bool
    ep3DirectionalRatioApproxOneSixthObservedIsTrue :
      ep3DirectionalRatioApproxOneSixthObserved ≡ true

    ep3ConservativeQuarterTargetRecorded : Bool
    ep3ConservativeQuarterTargetRecordedIsTrue :
      ep3ConservativeQuarterTargetRecorded ≡ true

    ep3QuotientAwareTransportAnsatzInstalled : Bool
    ep3QuotientAwareTransportAnsatzInstalledIsTrue :
      ep3QuotientAwareTransportAnsatzInstalled ≡ true

    ep3PrincipalTermBudgeted : Bool
    ep3PrincipalTermBudgetedIsFalse :
      ep3PrincipalTermBudgeted ≡ false

    ep3CrossDefectBudgeted : Bool
    ep3CrossDefectBudgetedIsFalse :
      ep3CrossDefectBudgeted ≡ false

    ep3PureDefectBudgeted : Bool
    ep3PureDefectBudgetedIsFalse :
      ep3PureDefectBudgeted ≡ false

    ep3DefectBudgetSubcritical : Bool
    ep3DefectBudgetSubcriticalIsFalse :
      ep3DefectBudgetSubcritical ≡ false

    ep3DirectionalBudgetProved : Bool
    ep3DirectionalBudgetProvedIsFalse :
      ep3DirectionalBudgetProved ≡ false

    ep3MarginClosingProved : Bool
    ep3MarginClosingProvedIsFalse :
      ep3MarginClosingProved ≡ false

    ep3Promoted : Bool
    ep3PromotedIsFalse :
      ep3Promoted ≡ false

open NSTriadKNGate2AEP3DirectionalTransportBudget public

canonicalNSTriadKNGate2AEP3DirectionalTransportBudget :
  NSTriadKNGate2AEP3DirectionalTransportBudget
canonicalNSTriadKNGate2AEP3DirectionalTransportBudget =
  mkNSTriadKNGate2AEP3DirectionalTransportBudget
    canonicalEP3Statuses
    refl
    canonicalEP3BudgetTerms
    refl
    canonicalEP3SampledShells
    refl
    canonicalBudgetFactorizationText
    refl
    canonicalRouteSelectionText
    refl
    canonicalObservedLedgerText
    refl
    canonicalImprovementText
    refl
    canonicalClosingText
    refl
    canonicalQuotientAwareText
    refl
    canonicalNSTriadKNGate2AQuotientAwareLiftDefectExpansion
    refl
    canonicalNSTriadKNGate2ASampledComparisonEnvelope
    refl
    canonicalNSTriadKNGate2AConeRestrictedDefectBudget
    refl
    canonicalDefectBudgetConsumptionText
    refl
    5
    refl
    3
    refl
    ep3SampledCoarseEnvelopeRejected
    ep3SampledDirectionalBelowQuarter
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
