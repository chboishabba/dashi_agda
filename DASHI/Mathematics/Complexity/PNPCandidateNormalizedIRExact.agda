module DASHI.Mathematics.Complexity.PNPCandidateNormalizedIRExact where

-- Flat interchange record. Actual alphabet cardinality is NOT the
-- padded arithmetic base; the one-symbol case has A=1, B=2.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat.Base using (_<_ ; _≤_ ; z≤n ; s≤s)
open import Data.Product using (_×_; _,_)
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

RuleBound : Nat → Nat → Rule → Set
RuleBound Q A (rule q a p b d) =
  (q < Q) × (a < A) × (p < Q) × (b < A) × (d < 3)

data RulesBound (Q A : Nat) : List Rule → Set where
  nil : RulesBound Q A []
  cons : ∀ {r rs} → RuleBound Q A r → RulesBound Q A rs → RulesBound Q A (r ∷ rs)

directionCode : L.Direction → Nat
directionCode L.moveLeft = 0
directionCode L.stayPut = 1
directionCode L.moveRight = 2

directionBound : ∀ d → directionCode d < 3
directionBound L.moveLeft = s≤s z≤n
directionBound L.stayPut = s≤s (s≤s z≤n)
directionBound L.moveRight = s≤s (s≤s (s≤s z≤n))

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

  normalizedRuleBound : ∀ r → RuleBound (C.StateWidth P.D.concrete)
    (C.listLength D.alphabet) (normalizeRule r)
  normalizedRuleBound (E.indexed-rule q a p b d) =
    toℕ<n q , P.actualDigitBound (E.symbolRead a) ,
    toℕ<n p , P.actualDigitBound (E.symbolRead b) , directionBound d

  normalizedRulesBound : ∀ rs → RulesBound (C.StateWidth P.D.concrete)
    (C.listLength D.alphabet) (map normalizeRule rs)
  normalizedRulesBound [] = nil
  normalizedRulesBound (r ∷ rs) = cons (normalizedRuleBound r) (normalizedRulesBound rs)

  exportedBounds : RulesBound (IR.states actualIR) (IR.alphabet actualIR) (IR.rules actualIR)
  exportedBounds = normalizedRulesBound P.E.exportedRules

  initialBound : IR.initial actualIR < IR.states actualIR
  initialBound = toℕ<n (E.initialFromBits (Candidate.candidateProgramBits standard))

  acceptingBound : IR.accepting actualIR < IR.states actualIR
  acceptingBound = toℕ<n (E.acceptingFromBits (Candidate.candidateProgramBits standard))

  originalBlank : D.digit (L.blank P.D.concrete) ≡ zero
  originalBlank = D.blankZero

  -- Export and native decodedEndpoint share standard, not an arbitrary
  -- replacement rule table. Duplicate enumeration witnesses are handled
  -- by the actual rank/read owners, not by assuming Fin index bijection.
  originalEndpoint = P.parsedEndpoint
  wire = flatten actualIR
