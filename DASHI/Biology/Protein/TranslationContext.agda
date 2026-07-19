module DASHI.Biology.Protein.TranslationContext where

open import Agda.Builtin.List using (List)

-- RNA alphabet used by the translation surface.  DNA-to-RNA transcription is a
-- separate bridge; translation consumes codons in a selected biological code.
data RNABase : Set where
  A C G U : RNABase

record Codon : Set where
  constructor codon
  field
    first second third : RNABase

open Codon public

data TranslationSignal (AminoAcid : Set) : Set where
  amino : AminoAcid → TranslationSignal AminoAcid
  stop  : TranslationSignal AminoAcid

-- Canonical nuclear, mitochondrial, ciliate, and other code tables are
-- instances of this interface.  Codon meaning is therefore context-indexed.
record TranslationContext : Set₁ where
  field
    AminoAcid : Set
    Context   : Set

    decode    : Context → Codon → TranslationSignal AminoAcid
    StartAllowed : Context → Codon → Set
    StopRecognised : Context → Codon → Set

record TranslationSystem
  (T : TranslationContext) : Set₁ where
  open TranslationContext T
  field
    Transcript : Set
    ProteinSequence : Set

    codons : Transcript → List Codon
    residues : ProteinSequence → List AminoAcid

    Translates : Context → Transcript → ProteinSequence → Set
    CorrectTermination : Context → Transcript → ProteinSequence → Set

record TranslationWitness
  {T : TranslationContext}
  (S : TranslationSystem T) : Set₁ where
  open TranslationContext T
  open TranslationSystem S
  field
    context    : Context
    transcript : Transcript
    protein    : ProteinSequence

    translates : Translates context transcript protein
    terminates : CorrectTermination context transcript protein

-- This witness records that one codon can have distinct meanings in different
-- translation contexts.  No global context-free codon decoder is postulated.
record ContextDependentCodonMeaning
  (T : TranslationContext) : Set₁ where
  open TranslationContext T
  field
    context₁ context₂ : Context
    selectedCodon     : Codon
    meaningsDiffer    : Set

-- Translation is only one leg of the central-dogma-shaped pipeline.  Folding,
-- localisation, modification, interaction, and function require later bridges.
record SequenceRecoveryBoundary
  (T : TranslationContext) : Set₁ where
  field
    TranscriptionRecovered : Set
    ReadingFrameRecovered  : Set
    TranslationRecovered   : Set

    transcriptionWitness : TranscriptionRecovered
    readingFrameWitness  : ReadingFrameRecovered
    translationWitness   : TranslationRecovered
