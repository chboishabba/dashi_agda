module DASHI.Foundations.Wette1969InitialRuleTranscriptionExact where

------------------------------------------------------------------------
-- WETTE 1969 INITIAL EXACT RULE TRANSCRIPTION
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Primary source locus: printed p.144, opening of the pure calculus:
--
--   0.1   -> k 0
--   0.2   k w -> k (' w)
--
-- The point of this module is methodological as much as mathematical: these
-- are the first rule *bodies* copied into the historical typed syntax.  Later
-- rule transcription should extend this same carrier rather than invent a
-- parallel operational encoding.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
import Data.Fin as Fin

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision

------------------------------------------------------------------------
-- A source rule has a fixed premise count, an ordered premise vector and one
-- conclusion.  Wette's printed comma-separated multiple conclusions are a
-- typographical abbreviation for several rules with the same premises, so the
-- atomic transcription carrier keeps one conclusion per rule.
------------------------------------------------------------------------

record HistoricalRuleBody : Set where
  constructor historicalRuleBody
  field
    address : Revision.HistoricalRuleAddress
    premiseCount : Nat
    premises : Vec Signature.Formula premiseCount
    conclusion : Signature.Formula

open HistoricalRuleBody public

------------------------------------------------------------------------
-- Small constructors for the source syntax.
------------------------------------------------------------------------

w : Signature.WordTerm
w = Signature.variableWordTerm Fin.zero

zeroTerm : Signature.WordTerm
zeroTerm = Signature.constantWordTerm Signature.zeroConstant

successor : Signature.WordTerm → Signature.WordTerm
successor term =
  Signature.unaryWordTerm Signature.successorFunctor refl term

naturalFormula : Signature.WordTerm → Signature.Formula
naturalFormula term =
  Signature.historicalFormula
    Signature.naturalNumberRelator
    (term ∷ᵥ []ᵥ)

------------------------------------------------------------------------
-- Rule 0.1: zero is a natural number.
------------------------------------------------------------------------

rule0-1Address : Revision.HistoricalRuleAddress
rule0-1Address = Revision.historicalRuleAddress 0 0 1

rule0-1 : HistoricalRuleBody
rule0-1 =
  historicalRuleBody
    rule0-1Address
    0
    []ᵥ
    (naturalFormula zeroTerm)

------------------------------------------------------------------------
-- Rule 0.2: from k(w), infer k('w).
------------------------------------------------------------------------

rule0-2Address : Revision.HistoricalRuleAddress
rule0-2Address = Revision.historicalRuleAddress 0 0 2

rule0-2 : HistoricalRuleBody
rule0-2 =
  historicalRuleBody
    rule0-2Address
    1
    (naturalFormula w ∷ᵥ []ᵥ)
    (naturalFormula (successor w))

------------------------------------------------------------------------
-- Exact source-visible regression facts.
------------------------------------------------------------------------

rule01HasZeroPremises : premiseCount rule0-1 ≡ 0
rule01HasZeroPremises = refl

rule02HasOnePremise : premiseCount rule0-2 ≡ 1
rule02HasOnePremise = refl

record Wette1969InitialRuleTranscriptionBoundary : Set where
  constructor wette1969InitialRuleTranscriptionBoundary
  field
    firstRuleBodiesTranscribed : Bool
    firstRuleBodiesTranscribedIsTrue : firstRuleBodiesTranscribed ≡ true

    transcriptionUsesHistoricalTypedSyntax : Bool
    transcriptionUsesHistoricalTypedSyntaxIsTrue :
      transcriptionUsesHistoricalTypedSyntax ≡ true

    twoRulesAlreadyConstituteCompleteHistoricalMachine : Bool
    twoRulesAlreadyConstituteCompleteHistoricalMachineIsFalse :
      twoRulesAlreadyConstituteCompleteHistoricalMachine ≡ false

    typographicalSharedPremiseAbbreviationIsOneMultiConclusionRule : Bool
    typographicalSharedPremiseAbbreviationIsOneMultiConclusionRuleIsFalse :
      typographicalSharedPremiseAbbreviationIsOneMultiConclusionRule ≡ false

canonicalWette1969InitialRuleTranscriptionBoundary :
  Wette1969InitialRuleTranscriptionBoundary
canonicalWette1969InitialRuleTranscriptionBoundary =
  wette1969InitialRuleTranscriptionBoundary
    true refl
    true refl
    false refl
    false refl
