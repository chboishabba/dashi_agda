module DASHI.Mathematics.Complexity.PNPCandidateNormalizedIRExact where

-- Flat interchange record. Actual alphabet cardinality is NOT the
-- padded arithmetic base; the one-symbol case has A=1, B=2.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (toℕ)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)
import DASHI.Mathematics.Complexity.PNPActualCandidateParsedEndpointExact as Parsed
import DASHI.Mathematics.Complexity.PNPStandardCandidateRuleExportExact as Export
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as C
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as Code

record Rule : Set where
  constructor rule
  field
    source read target write move : Nat

record IR : Set where
  constructor ir
  field
    states alphabet initial accepting : Nat
    rules : List Rule

directionCode : L.Direction → Nat
directionCode L.moveLeft = 0
directionCode L.stayPut = 1
directionCode L.moveRight = 2

flattenRules : List Rule → List Nat
flattenRules [] = []
flattenRules (rule q a p b d ∷ rs) = q ∷ a ∷ p ∷ b ∷ d ∷ flattenRules rs

flatten : IR → List Nat
flatten (ir Q A q p rs) = Q ∷ A ∷ q ∷ p ∷ C.listLength rs ∷ flattenRules rs

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

module Actual {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  {candidate : Direct.PolynomialSATDeciderCandidate cost}
  (standard : Candidate.StandardFiniteCandidateCode candidate) where

  module P = Parsed.Actual standard
  module E = P.E.E
  module D = P.D.D

  normalizeRule : E.IndexedRule → Rule
  normalizeRule (E.indexed-rule q a p b d) =
    rule (toℕ q) (P.normalizedExportDigit a)
      (toℕ p) (P.normalizedExportDigit b) (directionCode d)

  originalRule : L.TapeRule (L.State P.D.concrete) (L.Symbol P.D.concrete) → Rule
  originalRule (L.tape-rule q a p b d) =
    rule (toℕ (E.stateIndex q)) (D.digit a)
      (toℕ (E.stateIndex p)) (D.digit b) (directionCode d)

  normalizeEncoded : ∀ r → normalizeRule (E.encodeRule r) ≡ originalRule r
  normalizeEncoded (L.tape-rule q a p b d)
    rewrite P.normalizedOriginalDigit a | P.normalizedOriginalDigit b = refl

  normalizeList : ∀ rs → map normalizeRule (E.encodeRules rs) ≡ map originalRule rs
  normalizeList [] = refl
  normalizeList (r ∷ rs) = cong₂ _∷_ (normalizeEncoded r) (normalizeList rs)

  actualIR : IR
  actualIR = ir (C.StateWidth P.D.concrete) (C.listLength D.alphabet)
    (toℕ (E.initialFromBits (Candidate.candidateProgramBits standard)))
    (toℕ (E.acceptingFromBits (Candidate.candidateProgramBits standard)))
    (map normalizeRule P.E.exportedRules)

  -- Retain actual canonical decoded rules, without deduplication or
  -- reordering. This theorem is deliberately stated through fromBits.
  normalizedFromDecoded :
    ∀ rs → map normalizeRule (E.encodeRules rs) ≡ map originalRule rs
  normalizedFromDecoded = normalizeList

  actualRuleOrder : IR.rules actualIR ≡ map originalRule (L.rules P.D.concrete)
  actualRuleOrder = trans
    (normalizeList (Code.decodeProgramRules P.D.concrete
      (Candidate.candidateStateCoverage standard) (Candidate.candidateSymbolCoverage standard)
      (Candidate.candidateProgramBits standard)))
    (cong (map originalRule) (Code.decodeStaticProgramRules P.D.concrete
      (Candidate.candidateStateCoverage standard) (Candidate.candidateSymbolCoverage standard)))

  originalBlank : D.digit (L.blank P.D.concrete) ≡ zero
  originalBlank = D.blankZero

  -- Export and native decodedEndpoint share standard, not an arbitrary
  -- replacement rule table. Duplicate enumeration witnesses are handled
  -- by the actual rank/read owners, not by assuming Fin index bijection.
  originalEndpoint = P.parsedEndpoint
  wire = flatten actualIR
