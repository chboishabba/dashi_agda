module DASHI.Crypto.TranscriptProtectedLabelExact where

------------------------------------------------------------------------
-- PROTECTED-LABEL RECOVERY FROM OBSERVATION TRANSCRIPTS
--
-- Full hidden-state inversion is stronger than necessary.  A security failure
-- already exists if the protected output label factors through the observation
-- transcript.  Conversely, a single observation fibre carrying two different
-- protected labels refutes deterministic exact transcript recovery.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record TranscriptLabelSystem : Set₁ where
  constructor transcriptLabelSystem
  field
    Hidden TranscriptSummary ProtectedLabel : Set
    summarize : Hidden → TranscriptSummary
    label : Hidden → ProtectedLabel

open TranscriptLabelSystem public

record ExactTranscriptLabelRecovery
    (system : TranscriptLabelSystem) : Set₁ where
  constructor exactTranscriptLabelRecovery
  field
    recover : TranscriptSummary system → ProtectedLabel system
    exact : ∀ hidden →
      recover (summarize system hidden) ≡ label system hidden

open ExactTranscriptLabelRecovery public

record TranscriptLabelFibreSplit
    (system : TranscriptLabelSystem) : Set where
  constructor transcriptLabelFibreSplit
  field
    left right : Hidden system
    sameTranscript : summarize system left ≡ summarize system right
    labelsDiffer : label system left ≡ label system right → ⊥

open TranscriptLabelFibreSplit public

transcriptLabelSplitRefutesExactRecovery :
  ∀ {system : TranscriptLabelSystem} →
  TranscriptLabelFibreSplit system →
  ExactTranscriptLabelRecovery system → ⊥
transcriptLabelSplitRefutesExactRecovery {system} split recovery =
  labelsDiffer split labelEquality
  where
  labelEquality : label system (left split) ≡ label system (right split)
  labelEquality =
    trans
      (sym (exact recovery (left split)))
      (trans
        (cong (recover recovery) (sameTranscript split))
        (exact recovery (right split)))

------------------------------------------------------------------------
-- Intermediate public factorisation is enough for exact label recovery.
------------------------------------------------------------------------

record TranscriptLabelFactorisation
    (system : TranscriptLabelSystem) : Set₁ where
  constructor transcriptLabelFactorisation
  field
    Intermediate : Set
    quotient : TranscriptSummary system → Intermediate
    decode : Intermediate → ProtectedLabel system
    factorLaw : ∀ hidden →
      decode (quotient (summarize system hidden)) ≡ label system hidden

open TranscriptLabelFactorisation public

factorisationGivesExactTranscriptRecovery :
  ∀ {system : TranscriptLabelSystem} →
  TranscriptLabelFactorisation system →
  ExactTranscriptLabelRecovery system
factorisationGivesExactTranscriptRecovery factorisation =
  exactTranscriptLabelRecovery
    (λ summary → decode factorisation (quotient factorisation summary))
    (factorLaw factorisation)

transcriptLabelSplitRefutesFactorisation :
  ∀ {system : TranscriptLabelSystem} →
  TranscriptLabelFibreSplit system →
  TranscriptLabelFactorisation system → ⊥
transcriptLabelSplitRefutesFactorisation split factorisation =
  transcriptLabelSplitRefutesExactRecovery split
    (factorisationGivesExactTranscriptRecovery factorisation)
