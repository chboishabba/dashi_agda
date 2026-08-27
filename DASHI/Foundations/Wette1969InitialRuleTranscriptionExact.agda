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
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
import Data.Fin as Fin

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgement
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision

record HistoricalRuleBody : Set where
  constructor historicalRuleBody
  field
    address : Revision.HistoricalRuleAddress
    premiseCount : Nat
    premises : Vec Signature.Formula premiseCount
    conclusion : Signature.Formula

open HistoricalRuleBody public

w : Signature.WordTerm
w = Signature.variableWordTerm Fin.zero

zeroTerm : Signature.WordTerm
zeroTerm = Signature.constantWordTerm Signature.zeroConstant

successor : Signature.WordTerm → Signature.WordTerm
successor term =
  Signature.unaryWordTerm Signature.successorFunctor refl term

rule0-1Address : Revision.HistoricalRuleAddress
rule0-1Address = Revision.historicalRuleAddress 0 0 1

rule0-1 : HistoricalRuleBody
rule0-1 =
  historicalRuleBody
    rule0-1Address
    0
    []ᵥ
    (Judgement.naturalNumber zeroTerm)

rule0-2Address : Revision.HistoricalRuleAddress
rule0-2Address = Revision.historicalRuleAddress 0 0 2

rule0-2 : HistoricalRuleBody
rule0-2 =
  historicalRuleBody
    rule0-2Address
    1
    (Judgement.naturalNumber w ∷ᵥ []ᵥ)
    (Judgement.naturalNumber (successor w))

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

    sharedJudgementConstructorOwnerReused : Bool
    sharedJudgementConstructorOwnerReusedIsTrue :
      sharedJudgementConstructorOwnerReused ≡ true

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
    true refl
    false refl
    false refl
