module DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalCutsetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalDiscriminatorExact as Minimal

------------------------------------------------------------------------
-- Claim-specific cutsets for the four-axis Mabo doctrinal discriminator.
------------------------------------------------------------------------

record MinimalDoctrinalCutset : Set where
  constructor minimalDoctrinalCutset
  field
    existenceContinuityClosed : Bool
    recognitionConditionClosed : Bool
    recognitionEvidenceClosed : Bool
    extinguishmentClosed : Bool
    sourceIdentityClosed : Bool
    authorityInterpretationClosed : Bool
    cutsetReference : String
open MinimalDoctrinalCutset public

data MinimalFirstResidual : Set where
  sourceIdentityResidual
  existenceContinuityResidual
  recognitionConditionResidual
  recognitionEvidenceResidual
  extinguishmentResidual
  authorityInterpretationResidual
  unifiedReconciliationResidual
  minimalDoctrinalClosed
  : MinimalFirstResidual

firstResidual : Minimal.MinimalDoctrinalQuery → MinimalDoctrinalCutset → MinimalFirstResidual
firstResidual Minimal.identifyExistenceContinuity c with sourceIdentityClosed c
... | false = sourceIdentityResidual
... | true with existenceContinuityClosed c
...   | false = existenceContinuityResidual
...   | true = minimalDoctrinalClosed
firstResidual Minimal.identifyRecognitionCondition c with sourceIdentityClosed c
... | false = sourceIdentityResidual
... | true with recognitionConditionClosed c
...   | false = recognitionConditionResidual
...   | true with authorityInterpretationClosed c
...     | false = authorityInterpretationResidual
...     | true = minimalDoctrinalClosed
firstResidual Minimal.identifyRecognitionEvidence c with sourceIdentityClosed c
... | false = sourceIdentityResidual
... | true with recognitionEvidenceClosed c
...   | false = recognitionEvidenceResidual
...   | true = minimalDoctrinalClosed
firstResidual Minimal.identifyExtinguishmentRule c with sourceIdentityClosed c
... | false = sourceIdentityResidual
... | true with extinguishmentClosed c
...   | false = extinguishmentResidual
...   | true = minimalDoctrinalClosed
firstResidual Minimal.identifyUnifiedRecognitionTheory c with sourceIdentityClosed c
... | false = sourceIdentityResidual
... | true with existenceContinuityClosed c
...   | false = existenceContinuityResidual
...   | true with recognitionConditionClosed c
...     | false = recognitionConditionResidual
...     | true with recognitionEvidenceClosed c
...       | false = recognitionEvidenceResidual
...       | true with extinguishmentClosed c
...         | false = extinguishmentResidual
...         | true with authorityInterpretationClosed c
...           | false = authorityInterpretationResidual
...           | true = unifiedReconciliationResidual

------------------------------------------------------------------------
-- Canonical post-verification cutset.
--
-- Hall/Amodu source identity is paid. Continuity and extinguishment are
-- sufficiently sourced for narrow consumers. Recognition-condition
-- interpretation and recognition-evidence analysis remain separate.
------------------------------------------------------------------------

postHallVerificationCutset : MinimalDoctrinalCutset
postHallVerificationCutset = minimalDoctrinalCutset
  true
  false
  false
  true
  true
  false
  "authoritative Hall verification + text-native Amodu pay source identity; continuity/extinguishment narrow source questions close while recognition interpretation/evidence remain open"

continuityCanCloseWhileRecognitionConditionOpen :
  firstResidual Minimal.identifyExistenceContinuity postHallVerificationCutset ≡ minimalDoctrinalClosed
continuityCanCloseWhileRecognitionConditionOpen = refl

extinguishmentCanCloseWhileRecognitionEvidenceOpen :
  firstResidual Minimal.identifyExtinguishmentRule postHallVerificationCutset ≡ minimalDoctrinalClosed
extinguishmentCanCloseWhileRecognitionEvidenceOpen = refl

recognitionConditionStopsAtCondition :
  firstResidual Minimal.identifyRecognitionCondition postHallVerificationCutset ≡ recognitionConditionResidual
recognitionConditionStopsAtCondition = refl

recognitionEvidenceStopsAtEvidence :
  firstResidual Minimal.identifyRecognitionEvidence postHallVerificationCutset ≡ recognitionEvidenceResidual
recognitionEvidenceStopsAtEvidence = refl

unifiedTheoryStopsAtRecognitionCondition :
  firstResidual Minimal.identifyUnifiedRecognitionTheory postHallVerificationCutset ≡ recognitionConditionResidual
unifiedTheoryStopsAtRecognitionCondition = refl

------------------------------------------------------------------------
-- Independent closure fixtures demonstrate non-linearity.
------------------------------------------------------------------------

recognitionConditionOnlyClosed : MinimalDoctrinalCutset
recognitionConditionOnlyClosed = minimalDoctrinalCutset
  false true false false true true
  "recognition-condition consumer paid while continuity/evidence/extinguishment remain unresolved"

recognitionConditionCanCloseWithoutContinuity :
  firstResidual Minimal.identifyRecognitionCondition recognitionConditionOnlyClosed ≡ minimalDoctrinalClosed
recognitionConditionCanCloseWithoutContinuity = refl

recognitionConditionClosureDoesNotCloseContinuity :
  firstResidual Minimal.identifyExistenceContinuity recognitionConditionOnlyClosed ≡ existenceContinuityResidual
recognitionConditionClosureDoesNotCloseContinuity = refl

data NarrowClosureRequiresUnifiedTheory : Set where
data ContinuityClosurePaysRecognitionCondition : Set where
data ExtinguishmentClosurePaysRecognitionEvidence : Set where
data RecognitionConditionClosurePaysContinuity : Set where

data OneGlobalDoctrinalCutsetFitsEveryQuery : Set where

narrowClosureDoesNotRequireUnifiedTheory : NarrowClosureRequiresUnifiedTheory → ⊥
narrowClosureDoesNotRequireUnifiedTheory ()
continuityDoesNotPayRecognitionCondition : ContinuityClosurePaysRecognitionCondition → ⊥
continuityDoesNotPayRecognitionCondition ()
extinguishmentDoesNotPayRecognitionEvidence : ExtinguishmentClosurePaysRecognitionEvidence → ⊥
extinguishmentDoesNotPayRecognitionEvidence ()
recognitionConditionDoesNotPayContinuity : RecognitionConditionClosurePaysContinuity → ⊥
recognitionConditionDoesNotPayContinuity ()
oneGlobalCutsetDoesNotFitEveryQuery : OneGlobalDoctrinalCutsetFitsEveryQuery → ⊥
oneGlobalCutsetDoesNotFitEveryQuery ()
