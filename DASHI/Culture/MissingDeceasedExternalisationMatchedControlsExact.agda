module DASHI.Culture.MissingDeceasedExternalisationMatchedControlsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TechnicalExternalisationDepthBidiExact as X
import DASHI.Core.ExternalisationMatchedControlScoringExact as C
import DASHI.Culture.MissingDeceasedRosterEnrichmentDesignExact as D

------------------------------------------------------------------------
-- FIRST MATCHED-CONTROL STRATUM: MIT PSFC / fusion-plasma research
--
-- These are seed controls, not a completed denominator. Official MIT/PSFC
-- profiles are used only for the stages they actually expose. Unknown stages
-- stay stageNotInspected and therefore cannot be counted as absent.
------------------------------------------------------------------------

loureiroModel : C.StageEvidenceReceipt
loureiroModel = C.stage-evidence-receipt
  X.physicalOrTechnicalModel C.stagePresent
  "Loureiro et al., Viriato, CPC 206 (2016), DOI 10.1016/j.cpc.2016.05.004"
  "The public paper exposes the reduced-gyrokinetic physical model."

loureiroMethod : C.StageEvidenceReceipt
loureiroMethod = C.stage-evidence-receipt
  X.algorithmOrDesignMethod C.stagePresent
  "Loureiro et al., Viriato, CPC 206 (2016), DOI 10.1016/j.cpc.2016.05.004"
  "The public paper exposes the Hermite/pseudo-spectral numerical method and operator treatment."

loureiroValidation : C.StageEvidenceReceipt
loureiroValidation = C.stage-evidence-receipt
  X.benchmarkOrValidation C.stagePresent
  "Loureiro et al., Viriato, CPC 206 (2016), DOI 10.1016/j.cpc.2016.05.004; MIT PSFC profile"
  "The work publicly reports an extensive benchmark/validation programme."

loureiroSubject : C.MatchedExternalisationSubject
loureiroSubject = C.matched-externalisation-subject
  "Nuno F. G. Loureiro / Viriato"
  "MIT PSFC fusion/plasma theory-computation"
  "Roster subject matched within institution, fusion/plasma domain, senior research role and public publication opportunity."
  (loureiroModel ∷ loureiroMethod ∷ loureiroValidation ∷ [])

loureiroModelPositive : C.PositiveStage loureiroSubject X.physicalOrTechnicalModel
loureiroModelPositive = C.positive-stage loureiroModel C.hereReceipt refl refl

loureiroMethodPositive : C.PositiveStage loureiroSubject X.algorithmOrDesignMethod
loureiroMethodPositive = C.positive-stage loureiroMethod (C.thereReceipt C.hereReceipt) refl refl

loureiroValidationPositive : C.PositiveStage loureiroSubject X.benchmarkOrValidation
loureiroValidationPositive = C.positive-stage loureiroValidation (C.thereReceipt (C.thereReceipt C.hereReceipt)) refl refl

loureiroDeepScore : C.DeepExternalisationScore loureiroSubject
loureiroDeepScore = C.deep-externalisation-score
  loureiroModelPositive
  loureiroMethodPositive
  loureiroValidationPositive
  "Same three-stage rubric as controls: model + method + validation are all positively receipted."

------------------------------------------------------------------------
-- Anne White: immediate same-institution control capable of satisfying the same
-- deep rule. Her PSFC/NSE profiles explicitly describe turbulent-transport
-- models, diagnostic development, and transport-model validation.
------------------------------------------------------------------------

whiteModel : C.StageEvidenceReceipt
whiteModel = C.stage-evidence-receipt
  X.physicalOrTechnicalModel C.stagePresent
  "MIT PSFC Anne White profile; MIT NSE Anne White profile"
  "Official profiles describe models of turbulent transport and nonlinear gyrokinetic-code validation."

whiteMethod : C.StageEvidenceReceipt
whiteMethod = C.stage-evidence-receipt
  X.algorithmOrDesignMethod C.stagePresent
  "MIT PSFC Anne White profile"
  "Official profile describes development and use of diagnostic techniques for simultaneous turbulence measurements."

whiteValidation : C.StageEvidenceReceipt
whiteValidation = C.stage-evidence-receipt
  X.benchmarkOrValidation C.stagePresent
  "MIT PSFC Anne White profile; MIT NSE Anne White profile"
  "Transport-model validation and validation of nonlinear gyrokinetic codes are explicit research activities."

whiteSubject : C.MatchedExternalisationSubject
whiteSubject = C.matched-externalisation-subject
  "Anne E. White"
  "MIT PSFC fusion/plasma transport and validation"
  "Same institution and fusion/plasma domain; senior MIT researcher with comparable public technical visibility and publication opportunity."
  (whiteModel ∷ whiteMethod ∷ whiteValidation ∷ [])

whiteModelPositive : C.PositiveStage whiteSubject X.physicalOrTechnicalModel
whiteModelPositive = C.positive-stage whiteModel C.hereReceipt refl refl

whiteMethodPositive : C.PositiveStage whiteSubject X.algorithmOrDesignMethod
whiteMethodPositive = C.positive-stage whiteMethod (C.thereReceipt C.hereReceipt) refl refl

whiteValidationPositive : C.PositiveStage whiteSubject X.benchmarkOrValidation
whiteValidationPositive = C.positive-stage whiteValidation (C.thereReceipt (C.thereReceipt C.hereReceipt)) refl refl

whiteDeepScore : C.DeepExternalisationScore whiteSubject
whiteDeepScore = C.deep-externalisation-score
  whiteModelPositive
  whiteMethodPositive
  whiteValidationPositive
  "Anne White is a control-side deep-positive under the same model + method + validation rule; this prevents Loureiro from being treated as uniquely deep from the current rubric."

------------------------------------------------------------------------
-- Paul Bonoli: strong model/method/implementation evidence, validation stage not
-- yet inspected at publication level in this pass.
------------------------------------------------------------------------

bonoliModel : C.StageEvidenceReceipt
bonoliModel = C.stage-evidence-receipt
  X.physicalOrTechnicalModel C.stagePresent
  "MIT PSFC Paul Bonoli profile"
  "Profile describes detailed simulation models for RF heating/current-drive experiments and integrated calculations."

bonoliMethod : C.StageEvidenceReceipt
bonoliMethod = C.stage-evidence-receipt
  X.algorithmOrDesignMethod C.stagePresent
  "MIT PSFC Paul Bonoli profile"
  "Profile describes theoretical/computational methods including wave propagation, Fokker-Planck and transport calculations."

bonoliValidation : C.StageEvidenceReceipt
bonoliValidation = C.stage-evidence-receipt
  X.benchmarkOrValidation C.stageNotInspected
  "MIT PSFC Paul Bonoli profile only in this pass"
  "The profile establishes substantial modeling/method work but this pass has not yet inspected a comparable publication-level validation/benchmark receipt."

bonoliSubject : C.MatchedExternalisationSubject
bonoliSubject = C.matched-externalisation-subject
  "Paul T. Bonoli"
  "MIT PSFC plasma theory and computation"
  "Same institution, computational plasma/fusion domain, senior research role and public technical visibility."
  (bonoliModel ∷ bonoliMethod ∷ bonoliValidation ∷ [])

------------------------------------------------------------------------
-- Dennis Whyte: highly public fusion design/engineering work, but the current
-- profile-level pass does not yet close the exact model+method+validation triad.
------------------------------------------------------------------------

whyteModel : C.StageEvidenceReceipt
whyteModel = C.stage-evidence-receipt
  X.physicalOrTechnicalModel C.stageNotInspected
  "MIT PSFC Dennis Whyte profile"
  "Profile establishes broad fusion-system design activity but this pass does not treat that alone as an inspected technical-model receipt."

whyteMethod : C.StageEvidenceReceipt
whyteMethod = C.stage-evidence-receipt
  X.algorithmOrDesignMethod C.stagePresent
  "MIT PSFC Dennis Whyte profile"
  "Profile describes repeated fusion technology design courses and concrete design concepts advanced through them."

whyteValidation : C.StageEvidenceReceipt
whyteValidation = C.stage-evidence-receipt
  X.benchmarkOrValidation C.stageNotInspected
  "MIT PSFC Dennis Whyte profile only in this pass"
  "Comparable publication-level validation evidence has not yet been inspected under the fixed rubric."

whyteSubject : C.MatchedExternalisationSubject
whyteSubject = C.matched-externalisation-subject
  "Dennis G. Whyte"
  "MIT PSFC fusion systems and technology"
  "Same institution, senior fusion leadership/research role and high public technical visibility; retained as a control even if later scoring weakens H_E."
  (whyteModel ∷ whyteMethod ∷ whyteValidation ∷ [])

------------------------------------------------------------------------
-- Cohort and current conclusion.
------------------------------------------------------------------------

mitPsfcSeedCohort : C.ExternalisationControlCohort
mitPsfcSeedCohort = C.externalisation-control-cohort
  D.openScienceExternalisationDesign
  (loureiroSubject ∷ [])
  (whiteSubject ∷ bonoliSubject ∷ whyteSubject ∷ [])
  "First PSFC stratum. Anne White is already a control-side deep-positive; Bonoli and Whyte remain incompletely inspected rather than negative. No enrichment claim is made from this seed cohort."

record CurrentMITExternalisationControlAssessment : Set where
  constructor current-mit-externalisation-control-assessment
  field
    loureiroDeepPositive : Bool
    loureiroDeepPositiveIsTrue : loureiroDeepPositive ≡ true
    whiteControlDeepPositive : Bool
    whiteControlDeepPositiveIsTrue : whiteControlDeepPositive ≡ true
    bonoliCompleteScore : Bool
    bonoliCompleteScoreIsFalse : bonoliCompleteScore ≡ false
    whyteCompleteScore : Bool
    whyteCompleteScoreIsFalse : whyteCompleteScore ≡ false
    loureiroUniquelyDeepWithinSeedControls : Bool
    loureiroUniquelyDeepWithinSeedControlsIsFalse :
      loureiroUniquelyDeepWithinSeedControls ≡ false
    enrichmentClosed : Bool
    enrichmentClosedIsFalse : enrichmentClosed ≡ false

canonicalCurrentMITExternalisationControlAssessment : CurrentMITExternalisationControlAssessment
canonicalCurrentMITExternalisationControlAssessment =
  current-mit-externalisation-control-assessment
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
