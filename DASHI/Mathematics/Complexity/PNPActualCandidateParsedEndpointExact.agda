module DASHI.Mathematics.Complexity.PNPActualCandidateParsedEndpointExact where

-- Original parser and finite blank-first digit owner share the same
-- StandardFiniteCandidateCode. No independent replacement program.
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (_<_)
import DASHI.Mathematics.Complexity.PNPStandardCandidateRuleExportExact as Export
import DASHI.Mathematics.Complexity.PNPStackFiniteDigitOwnerExact as Digits
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as C
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as Code
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as S
import Relation.Binary.PropositionalEquality using (cong; trans)

module Actual {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  {candidate : Direct.PolynomialSATDeciderCandidate cost}
  (standard : Candidate.StandardFiniteCandidateCode candidate) where

  module E = Export.ActualCandidate standard
  module D = Digits.Actual standard

  -- Stronger than the padded-base bound: dispatch uses the actual
  -- alphabet cardinality, even in the one-symbol case.
  actualDigitBound : ∀ a → D.D.digit a < C.listLength D.D.alphabet
  actualDigitBound a = Digits.rankBound (L.finiteSymbol D.concrete)
    (Digits.retain D.D.m (C.listed (Candidate.candidateSymbolCoverage standard) a))

  normalizedExportDigit : E.E.A → Nat
  normalizedExportDigit a = D.D.digit (E.E.symbolRead a)

  normalizedOriginalDigit : ∀ a →
    normalizedExportDigit (E.E.symbolIndex a) ≡ D.D.digit a
  normalizedOriginalDigit a = cong D.D.digit (E.E.symbolRoundtrip a)

  parsedBlankZero :
    normalizedExportDigit (E.E.blankFromBits (Candidate.candidateProgramBits standard))
    ≡ zero
  parsedBlankZero = trans (cong D.D.digit E.E.actualBlank) D.D.blankZero

  -- Rule order and decoded execution both refer to the original bits and
  -- same actual candidate, not a trace-specific compiled surrogate.
  parsedEndpoint : (f : Cook.BooleanFormula) →
    (E.E.decodeRules E.exportedRules ≡ L.rules D.concrete) ×
    (D.Decoded.NRun.decodeRun
      (D.Decoded.NRun.run (Candidate.exactSteps standard f)
        (D.Decoded.NRun.P.pack (D.Decoded.start f)))
      ≡ just (Candidate.finish standard f)) ×
    (L.decideEqual (L.finiteState D.concrete)
      (S.state (Candidate.finish standard f))
      (Code.acceptingControl D.ActualRun.programView)
      ≡ Direct.decide candidate f)
  parsedEndpoint f =
    E.exportedRulesExact , D.Decoded.decodedEndpoint f , D.Decoded.endpointDecision f

-- The Lean raw FRACTRAN word-bisim is a separate kernel proof. Actual
-- cross-language first-rule and inventory correspondence is not inferred
-- from these two exact original Agda endpoint statements.
