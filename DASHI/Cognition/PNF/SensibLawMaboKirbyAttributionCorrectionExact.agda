module DASHI.Cognition.PNF.SensibLawMaboKirbyAttributionCorrectionExact where

------------------------------------------------------------------------
-- MABO AUTHORSHIP / TEMPORAL ATTRIBUTION CORRECTION
--
-- Stable sources:
--   * Mabo v Queensland (No 2) [1992] HCA 23; 175 CLR 1.
--   * High Court of Australia, judicial service chronology: Michael Kirby was
--     appointed to the High Court in 1996, after Mabo (No 2) in 1992.
--   * Justice Michael Kirby, later speeches/writing discussing Mabo, including
--     "The Challenges to Justice in a Plural Society", High Court speech archive:
--     https://www.hcourt.gov.au/sites/default/files/assets/publications/speeches/former-justices/kirbyj/kirbyj_plural.htm
--
-- Therefore the principal Mabo (No 2) reasoning cannot be attributed to Kirby J.
-- The central majority reasoning discussed in this repository is Brennan J's,
-- with Mason CJ and McHugh J agreeing with his reasons; later Kirby commentary
-- is a distinct secondary/judicial-reflective source.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record AttributionCorrection : Set where
  constructor attribution-correction
  field
    proposition : String
    mistakenAttribution : String
    correctedAttribution : String
    temporalReason : String
    stableAuthority : String
    correctionEstablished : Bool

open AttributionCorrection public

maboPrincipalReasoningCorrection : AttributionCorrection
maboPrincipalReasoningCorrection = attribution-correction
  "principal Mabo (No 2) recognition/radical-title reasoning"
  "Kirby J"
  "Brennan J (Mason CJ and McHugh J agreeing with Brennan J's reasons)"
  "Mabo (No 2) was decided in 1992; Michael Kirby joined the High Court in 1996"
  "[1992] HCA 23; High Court of Australia judicial chronology and Kirby speech archive"
  true

data LaterCommentaryIsOriginalJudgmentAuthorship : Set where
laterKirbyCommentaryDoesNotRewriteAuthorship : LaterCommentaryIsOriginalJudgmentAuthorship → ⊥
laterKirbyCommentaryDoesNotRewriteAuthorship ()
