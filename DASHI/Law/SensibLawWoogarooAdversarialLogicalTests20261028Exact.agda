module DASHI.Law.SensibLawWoogarooAdversarialLogicalTests20261028Exact where

-- Woogaroo EPBC 2019/8575: finite adversarial logic, not a merits judgment.
-- Source provenance: Commonwealth EPBC 1999 Act as compiled 24 Aug 2026,
-- the Environment Protection Reform Act 2025 transition provisions,
-- original QUT/QCC submissions and Stockland first-party claims;
-- Tarkine [2013] FCA 694, Tarkine [2015] FCAFC 89,
-- ECCC [2024] FCAFC 56 and Rainforest Reserves [2025] FCA 532.
-- Original law, judgments, ecology and reporting retain their authorship.
-- Code: user-directed Johl Brown / ChatGPT-assisted adaptation.
-- Reuse original DASHI PNF logical calculus and fixed-width Bool semantics.
-- Reuse the older ForAgainst hole matrix, Pareto/snowball and current seven
-- grounds. No private-source receipt, Court filing, ministerial admission,
-- legal advice, kernel execution or automatic statute/application is implied.
-- The ancient for/against refusal/clock row is historical, not 2026 status.

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.PredicateNormalFormLogicalCalculusExact as Logic
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as PNF
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as Truth
import DASHI.Core.CounterexampleGuidedConsumerRefinementExact as Refinement
import DASHI.Core.ContradictionPreservingReasoningPipelineExact as Tension
import DASHI.Law.SensibLawWoogarooForAgainstLegalHoleMatrixExact as Historical
import DASHI.Law.SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact as Case
import DASHI.Law.SensibLawWoogarooEPBC20198575ApplicableLawMatrixExact as SavedLaw
import DASHI.Law.SensibLawWoogarooParetoSnowballAcquisitionExact as Pareto
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Ibrahim

------------------------------------------------------------------------
-- Same seven canonical grounds, not a new legal taxonomy.
------------------------------------------------------------------------

groundKey : Case.Ground → String
groundKey Case.approvedAdviceOmitted = "advice-consideration"
groundKey Case.recoveryPlanConflict = "recovery-plan"
groundKey Case.actionBaselineError = "incremental-habitat"
groundKey Case.commentTransmissionOrProcedure = "comment-transmission"
groundKey Case.scopeOrUncertainConditions = "approval-scope"
groundKey Case.sameStageCondition6aBreach = "local-prestart"
groundKey Case.improperPoliticalFinancialInfluence = "improper-influence"

allSeven : List Case.Ground
allSeven =
  Case.approvedAdviceOmitted ∷
  Case.recoveryPlanConflict ∷
  Case.actionBaselineError ∷
  Case.commentTransmissionOrProcedure ∷
  Case.scopeOrUncertainConditions ∷
  Case.sameStageCondition6aBreach ∷
  Case.improperPoliticalFinancialInfluence ∷ []

historicalForAgainst : Historical.ForAgainstHole
historicalForAgainst = Historical.epbc8575Hole

transitionalSection139 : SavedLaw.ApplicableRule
transitionalSection139 = SavedLaw.newPart9Sections138139

-- Formula labels are FORMAL atoms. They are not independently reviewed
-- PNF interpretations or empirical facts. Reuse the native PNF calculus.
premise : Case.Ground → PNF.Formula
premise g = PNF.atom (groundKey g) []

conditionalResult : Case.Ground → PNF.Formula
conditionalResult g = PNF.atom "hypothetical-legal-consequence" []

-- An applicant can derive a consequence only when the bridge/rule and
-- premise have BOTH been supplied. This proves a sequent, not either input.
conditionalApplicantDerivation : (g : Case.Ground) →
  Logic._⊢_
    (PNF._⇒_ (premise g) (conditionalResult g) ∷
      premise g ∷ [])
    (conditionalResult g)
conditionalApplicantDerivation g =
  Logic.impElim
    (Logic.assumption Logic.here)
    (Logic.assumption (Logic.there Logic.here))

-- The same logical rule is neutral to party identity. A genuine government
-- rebuttal likewise needs its own evidence + conditional statutory bridge.
defencePremise : Case.Ground → PNF.Formula
defencePremise g = PNF.atom "government-reviewed-compliance" []

defenceConsequence : Case.Ground → PNF.Formula
defenceConsequence g = PNF.atom "hypothetical-defence-result" []

conditionalRespondentDerivation : (g : Case.Ground) →
  Logic._⊢_
    (PNF._⇒_ (defencePremise g) (defenceConsequence g) ∷
      defencePremise g ∷ [])
    (defenceConsequence g)
conditionalRespondentDerivation g =
  Logic.impElim
    (Logic.assumption Logic.here)
    (Logic.assumption (Logic.there Logic.here))

------------------------------------------------------------------------
-- Boolean semantics reuse the FIXED-WIDTH truth-table owner.
-- The counterexamples refute unqualified Lead => LegalBridge under this
-- explicit unconstrained valuation. No statement about actual case facts.
------------------------------------------------------------------------

impliesBool : Bool → Bool → Bool
impliesBool lead link = Truth.orBool (Truth.notBool lead) link

record ShortcutCountermodel (g : Case.Ground) : Set where
  constructor shortcut-countermodel
  field
    observedLead : Bool
    requiredLegalBridge : Bool
    leadPresent : observedLead ≡ true
    bridgeNotEstablished : requiredLegalBridge ≡ false
    unconditionalInferenceFails :
      impliesBool observedLead requiredLegalBridge ≡ false
open ShortcutCountermodel public

-- Every canonical ground has a *finite* logical countermodel to a source
-- lead alone entailing its statutory/factual bridge. This is not a proof that
-- the required bridge is actually false at Woogaroo.
sourceLeadAloneIsInsufficient : (g : Case.Ground) →
  ShortcutCountermodel g
sourceLeadAloneIsInsufficient g =
  shortcut-countermodel true false refl refl refl

adviceShortcutCountermodel :
  ShortcutCountermodel Case.approvedAdviceOmitted
adviceShortcutCountermodel =
  sourceLeadAloneIsInsufficient Case.approvedAdviceOmitted

recoveryShortcutCountermodel :
  ShortcutCountermodel Case.recoveryPlanConflict
recoveryShortcutCountermodel =
  sourceLeadAloneIsInsufficient Case.recoveryPlanConflict

habitatShortcutCountermodel :
  ShortcutCountermodel Case.actionBaselineError
habitatShortcutCountermodel =
  sourceLeadAloneIsInsufficient Case.actionBaselineError

commentShortcutCountermodel :
  ShortcutCountermodel Case.commentTransmissionOrProcedure
commentShortcutCountermodel =
  sourceLeadAloneIsInsufficient Case.commentTransmissionOrProcedure

scopeShortcutCountermodel :
  ShortcutCountermodel Case.scopeOrUncertainConditions
scopeShortcutCountermodel =
  sourceLeadAloneIsInsufficient Case.scopeOrUncertainConditions

prestartShortcutCountermodel :
  ShortcutCountermodel Case.sameStageCondition6aBreach
prestartShortcutCountermodel =
  sourceLeadAloneIsInsufficient Case.sameStageCondition6aBreach

influenceShortcutCountermodel :
  ShortcutCountermodel Case.improperPoliticalFinancialInfluence
influenceShortcutCountermodel =
  sourceLeadAloneIsInsufficient Case.improperPoliticalFinancialInfluence

------------------------------------------------------------------------
-- Independent seven-ground hypothetical WORLDS: for, against, unknown.
-- This is a decision-table REFERENCE MODEL, not the real 2026 source state.
-- The stipulated "legal relevance" tests are not court-certified sufficiency.
------------------------------------------------------------------------

record HypotheticalWorld (g : Case.Ground) : Set where
  constructor world
  field
    legallyApplicable : Bool
    defectEstablished : Bool
    materialityEstablished : Bool
    governmentComplianceEstablished : Bool
    actualEvidenceReviewed : Bool
    ecologicalHarmAssumed : Bool
open HypotheticalWorld public

applicantConditional : ∀ {g} → HypotheticalWorld g → Bool
applicantConditional w =
  Truth.andBool (Truth.notBool (governmentComplianceEstablished w))
    (Truth.andBool (actualEvidenceReviewed w)
      (Truth.andBool (legallyApplicable w)
        (Truth.andBool (defectEstablished w)
          (materialityEstablished w))))

respondentConditional : ∀ {g} → HypotheticalWorld g → Bool
respondentConditional w =
  Truth.andBool (governmentComplianceEstablished w)
    (Truth.andBool (actualEvidenceReviewed w)
      (legallyApplicable w))

-- Hypotheticals ONLY, with explicitly stipulated reviewed-evidence flags.
-- There are NO such paid witnesses in the present SLR case model.
applicantWorld : (g : Case.Ground) → HypotheticalWorld g
applicantWorld g = world true true true false true true

respondentWorld : (g : Case.Ground) → HypotheticalWorld g
respondentWorld g = world true false false true true true

unresolvedWorld : (g : Case.Ground) → HypotheticalWorld g
unresolvedWorld g = world true false false false false true

applicantBranchPossible : (g : Case.Ground) →
  applicantConditional (applicantWorld g) ≡ true
applicantBranchPossible g = refl

respondentBranchPossible : (g : Case.Ground) →
  respondentConditional (respondentWorld g) ≡ true
respondentBranchPossible g = refl

unpaidSupportsNeitherApplicant : (g : Case.Ground) →
  applicantConditional (unresolvedWorld g) ≡ false
unpaidSupportsNeitherApplicant g = refl

unpaidSupportsNeitherRespondent : (g : Case.Ground) →
  respondentConditional (unresolvedWorld g) ≡ false
unpaidSupportsNeitherRespondent g = refl

-- A single consistent valuation cannot support *both* branches of this
-- stipulated decision profile. This is Boolean consistency, not a Court vote.
cannotPromoteOppositeBranches :
  ∀ {g} (w : HypotheticalWorld g) →
  applicantConditional w ≡ true →
  respondentConditional w ≡ true → ⊥
cannotPromoteOppositeBranches (world a b c false e f) _ ()
cannotPromoteOppositeBranches (world a b c true e f) () _

-- Habitat damage is not by itself the statutory omission. Conversely,
-- even a modelled government-compliance defence can coexist with damage.
harmWithoutLegalError : HypotheticalWorld Case.approvedAdviceOmitted
harmWithoutLegalError =
  world true false false true true true

harmDoesNotForceApplicantResult :
  applicantConditional harmWithoutLegalError ≡ false
harmDoesNotForceApplicantResult = refl

complianceDoesNotProveNoHarm :
  ecologicalHarmAssumed harmWithoutLegalError ≡ true
complianceDoesNotProveNoHarm = refl

respondentCouldPrevailDespiteHarm :
  respondentConditional harmWithoutLegalError ≡ true
respondentCouldPrevailDespiteHarm = refl

-- Approval publication, conservation submissions, original judgment analogy,
-- a court case elsewhere, or political/financial adjacency cannot fill these
-- live source payments. Witnesses above are pure hypothetical assignments.
data ActualWoogarooMeritsDischarge : Set where

noLiveDischargeFromLogicalScenarios :
  ActualWoogarooMeritsDischarge → ⊥
noLiveDischargeFromLogicalScenarios ()
