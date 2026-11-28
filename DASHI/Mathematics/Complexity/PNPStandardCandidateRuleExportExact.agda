module DASHI.Mathematics.Complexity.PNPStandardCandidateRuleExportExact where

-- Decode the SAME static candidate code, not a trace-specific program.
-- The existing genuine enumeration membership supplies every finite
-- index; decoding returns the original rule list in literal order.
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂; trans)
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as C
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as P
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate

lookup : ∀ {A : Set} (xs : List A) → Fin (C.listLength xs) → A
lookup [] ()
lookup (x ∷ xs) zero = x
lookup (x ∷ xs) (suc i) = lookup xs i

locate : ∀ {A : Set} (e : L.FiniteEnumeration A) (x : A)
  (xs : List A) → C.Member x xs →
  Σ (Fin (C.listLength xs)) (λ i → lookup xs i ≡ x)
locate e x (x ∷ xs) C.here = zero , refl
locate e x (y ∷ ys) (C.there p) with L.decideEqual e x y in eq
... | true = zero , sym (L.decideEqualSound e eq)
... | false with locate e x ys p
...   | i , h = suc i , h

module Export (machine : L.ConcreteTapeMachine)
    (sc : C.EnumerationCoverage (L.finiteState machine))
    (ac : C.EnumerationCoverage (L.finiteSymbol machine)) where

  Q : Set
  Q = Fin (C.StateWidth machine)

  A : Set
  A = Fin (C.SymbolWidth machine)

  stateIndex : L.State machine → Q
  stateIndex x = proj₁ (locate (L.finiteState machine) x
    (L.values (L.finiteState machine)) (C.listed sc x))

  symbolIndex : L.Symbol machine → A
  symbolIndex x = proj₁ (locate (L.finiteSymbol machine) x
    (L.values (L.finiteSymbol machine)) (C.listed ac x))

  stateRead : Q → L.State machine
  stateRead = lookup (L.values (L.finiteState machine))

  symbolRead : A → L.Symbol machine
  symbolRead = lookup (L.values (L.finiteSymbol machine))

  stateRoundtrip : ∀ x → stateRead (stateIndex x) ≡ x
  stateRoundtrip x = proj₂ (locate (L.finiteState machine) x
    (L.values (L.finiteState machine)) (C.listed sc x))

  symbolRoundtrip : ∀ x → symbolRead (symbolIndex x) ≡ x
  symbolRoundtrip x = proj₂ (locate (L.finiteSymbol machine) x
    (L.values (L.finiteSymbol machine)) (C.listed ac x))

  stateInjective : ∀ {x y} → stateIndex x ≡ stateIndex y → x ≡ y
  stateInjective {x} {y} h = trans (sym (stateRoundtrip x))
    (trans (cong stateRead h) (stateRoundtrip y))

  symbolInjective : ∀ {x y} → symbolIndex x ≡ symbolIndex y → x ≡ y
  symbolInjective {x} {y} h = trans (sym (symbolRoundtrip x))
    (trans (cong symbolRead h) (symbolRoundtrip y))

  record IndexedRule : Set where
    constructor indexed-rule
    field
      source : Q
      read : A
      target : Q
      write : A
      direction : L.Direction

  encodeRule : L.TapeRule (L.State machine) (L.Symbol machine) → IndexedRule
  encodeRule (L.tape-rule q a p b d) =
    indexed-rule (stateIndex q) (symbolIndex a) (stateIndex p) (symbolIndex b) d

  decodeRule : IndexedRule → L.TapeRule (L.State machine) (L.Symbol machine)
  decodeRule (indexed-rule q a p b d) =
    L.tape-rule (stateRead q) (symbolRead a) (stateRead p) (symbolRead b) d

  ruleRoundtrip : ∀ r → decodeRule (encodeRule r) ≡ r
  ruleRoundtrip (L.tape-rule q a p b d)
    rewrite stateRoundtrip q | symbolRoundtrip a
          | stateRoundtrip p | symbolRoundtrip b = refl

  encodeRules : List (L.TapeRule (L.State machine) (L.Symbol machine)) →
    List IndexedRule
  encodeRules [] = []
  encodeRules (r ∷ rs) = encodeRule r ∷ encodeRules rs

  decodeRules : List IndexedRule → List (L.TapeRule (L.State machine) (L.Symbol machine))
  decodeRules [] = []
  decodeRules (r ∷ rs) = decodeRule r ∷ decodeRules rs

  rulesRoundtrip : ∀ rs → decodeRules (encodeRules rs) ≡ rs
  rulesRoundtrip [] = refl
  rulesRoundtrip (r ∷ rs) = cong₂ _∷_ (ruleRoundtrip r) (rulesRoundtrip rs)

  fromBits : CNF.Bits (P.StaticProgramBitsWidth machine) → List IndexedRule
  fromBits bits = encodeRules (P.decodeProgramRules machine sc ac bits)

  actualRules : decodeRules (fromBits (P.encodeStaticProgram machine sc ac)) ≡ L.rules machine
  actualRules = trans (rulesRoundtrip (P.decodeProgramRules machine sc ac
    (P.encodeStaticProgram machine sc ac))) (P.decodeStaticProgramRules machine sc ac)

  blankFromBits : CNF.Bits (P.StaticProgramBitsWidth machine) → A
  blankFromBits bits = symbolIndex (P.decodeProgramBlank machine sc ac bits)

  initialFromBits : CNF.Bits (P.StaticProgramBitsWidth machine) → Q
  initialFromBits bits = stateIndex (P.decodeProgramInitialState machine sc ac bits)

  acceptingFromBits : CNF.Bits (P.StaticProgramBitsWidth machine) → Q
  acceptingFromBits bits = stateIndex (P.decodeProgramAcceptingState machine sc ac bits)

  actualBlank : symbolRead (blankFromBits (P.encodeStaticProgram machine sc ac)) ≡ L.blank machine
  actualBlank = trans (symbolRoundtrip (P.decodeProgramBlank machine sc ac
    (P.encodeStaticProgram machine sc ac))) (P.decodeStaticProgramBlank machine sc ac)

  actualInitial : stateRead (initialFromBits (P.encodeStaticProgram machine sc ac)) ≡ L.initialState machine
  actualInitial = trans (stateRoundtrip (P.decodeProgramInitialState machine sc ac
    (P.encodeStaticProgram machine sc ac))) (P.decodeStaticProgramInitial machine sc ac)

  actualAccepting : stateRead (acceptingFromBits (P.encodeStaticProgram machine sc ac)) ≡ L.acceptingState machine
  actualAccepting = trans (stateRoundtrip (P.decodeProgramAcceptingState machine sc ac
    (P.encodeStaticProgram machine sc ac))) (P.decodeStaticProgramAccepting machine sc ac)

module ActualCandidate
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (standard : Candidate.StandardFiniteCandidateCode candidate) where

  module E = Export (Candidate.candidateConcreteMachine standard)
    (Candidate.candidateStateCoverage standard)
    (Candidate.candidateSymbolCoverage standard)

  exportedRules : List E.IndexedRule
  exportedRules = E.fromBits (Candidate.candidateProgramBits standard)

  exportedRulesExact : E.decodeRules exportedRules ≡ L.rules (Candidate.candidateConcreteMachine standard)
  exportedRulesExact = E.actualRules

-- The exporter is indexed by the original finite presentation and codec.
-- It is not a universal parser of arbitrary bit strings, nor the
-- resource-closing fixed program compiler. Native kernel pending.
