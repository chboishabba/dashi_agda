module DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact where

------------------------------------------------------------------------
-- FINITE PROGRAM DESCRIPTION -> ORDINARY BOOLEAN FORMULA
--
-- A fixed candidate program's code is not the asymptotic obstacle in the
-- self-diagonal route.  This owner embeds the concrete static machine bitstring
-- into ordinary BooleanFormula syntax as a tautological payload.
--
-- Each source bit is represented by a syntactically distinct three-node
-- tautology:
--
--   true  -> (true  OR false)
--   false -> (false OR true)
--
-- and the tokens are conjoined.  The resulting formula is always satisfiable
-- and has exactly
--
--   4 * codeWidth + 1
--
-- syntax nodes: three token nodes plus one conjunction node per bit, and one
-- terminal true constant.
--
-- Therefore for a FIXED machine D, quoting its finite static program incurs a
-- fixed linear-in-program-code cost, independent of the size of the later
-- diagonal input.  The unresolved growth is the self-evaluation certificate,
-- not the existence of finite syntax for D.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as Program

------------------------------------------------------------------------
-- Formula size.
------------------------------------------------------------------------

formulaNodeCount : Cook.BooleanFormula → Nat
formulaNodeCount (Cook.variable index) =
  suc zero
formulaNodeCount (Cook.constant value) =
  suc zero
formulaNodeCount (Cook.negate formula) =
  suc (formulaNodeCount formula)
formulaNodeCount (Cook.conjunction left right) =
  suc (formulaNodeCount left + formulaNodeCount right)
formulaNodeCount (Cook.disjunction left right) =
  suc (formulaNodeCount left + formulaNodeCount right)

four : Nat
four = suc (suc (suc (suc zero)))

------------------------------------------------------------------------
-- Equal-size syntactically distinct tautological bit tokens.
------------------------------------------------------------------------

bitToken : Bool → Cook.BooleanFormula
bitToken true =
  Cook.disjunction
    (Cook.constant true)
    (Cook.constant false)
bitToken false =
  Cook.disjunction
    (Cook.constant false)
    (Cook.constant true)

bitTokenNodeCount :
  (bit : Bool) →
  formulaNodeCount (bitToken bit) ≡ suc (suc (suc zero))
bitTokenNodeCount true = refl
bitTokenNodeCount false = refl

bitTokenIsTautology :
  (bit : Bool) →
  (assignment : Cook.Assignment) →
  Cook.evaluate (bitToken bit) assignment ≡ true
bitTokenIsTautology true assignment = refl
bitTokenIsTautology false assignment = refl

------------------------------------------------------------------------
-- Width-indexed bit payload.
------------------------------------------------------------------------

embedBitsAsTautology :
  ∀ {width : Nat} →
  CNF.Bits width →
  Cook.BooleanFormula
embedBitsAsTautology CNF.[]ᵇ =
  Cook.constant true
embedBitsAsTautology (bit CNF.∷ᵇ rest) =
  Cook.conjunction
    (bitToken bit)
    (embedBitsAsTautology rest)

embedBitsNodeCount :
  ∀ {width : Nat}
    (bits : CNF.Bits width) →
  formulaNodeCount (embedBitsAsTautology bits)
  ≡ suc (four * width)
embedBitsNodeCount CNF.[]ᵇ =
  refl
embedBitsNodeCount (bit CNF.∷ᵇ rest)
    rewrite bitTokenNodeCount bit
          | embedBitsNodeCount rest =
  refl

embedBitsIsTautology :
  ∀ {width : Nat}
    (bits : CNF.Bits width)
    (assignment : Cook.Assignment) →
  Cook.evaluate (embedBitsAsTautology bits) assignment
  ≡ true
embedBitsIsTautology CNF.[]ᵇ assignment =
  refl
embedBitsIsTautology (bit CNF.∷ᵇ rest) assignment
    rewrite bitTokenIsTautology bit assignment
          | embedBitsIsTautology rest assignment =
  refl

embedBitsIsSatisfiable :
  ∀ {width : Nat}
    (bits : CNF.Bits width) →
  Cook.Satisfiable (embedBitsAsTautology bits)
embedBitsIsSatisfiable bits =
  Cook.satisfyingAssignment
    (λ index → false)
    (embedBitsIsTautology bits (λ index → false))

------------------------------------------------------------------------
-- Specialization to the literal concrete tape program code.
------------------------------------------------------------------------

staticProgramDescriptionFormula :
  (machine : Local.ConcreteTapeMachine)
  (stateCoverage :
    Canonical.EnumerationCoverage (Local.finiteState machine))
  (symbolCoverage :
    Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Cook.BooleanFormula
staticProgramDescriptionFormula
    machine stateCoverage symbolCoverage =
  embedBitsAsTautology
    (Program.encodeStaticProgram
      machine stateCoverage symbolCoverage)

staticProgramDescriptionFormulaNodeCount :
  (machine : Local.ConcreteTapeMachine)
  (stateCoverage :
    Canonical.EnumerationCoverage (Local.finiteState machine))
  (symbolCoverage :
    Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  formulaNodeCount
    (staticProgramDescriptionFormula
      machine stateCoverage symbolCoverage)
  ≡
  suc
    (four * Program.StaticProgramBitsWidth machine)
staticProgramDescriptionFormulaNodeCount
    machine stateCoverage symbolCoverage =
  embedBitsNodeCount
    (Program.encodeStaticProgram
      machine stateCoverage symbolCoverage)

staticProgramDescriptionFormulaIsSatisfiable :
  (machine : Local.ConcreteTapeMachine)
  (stateCoverage :
    Canonical.EnumerationCoverage (Local.finiteState machine))
  (symbolCoverage :
    Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Cook.Satisfiable
    (staticProgramDescriptionFormula
      machine stateCoverage symbolCoverage)
staticProgramDescriptionFormulaIsSatisfiable
    machine stateCoverage symbolCoverage =
  embedBitsIsSatisfiable
    (Program.encodeStaticProgram
      machine stateCoverage symbolCoverage)

------------------------------------------------------------------------
-- The quotation overhead is a machine constant.
------------------------------------------------------------------------

programQuotationOverhead :
  Local.ConcreteTapeMachine →
  Nat
programQuotationOverhead machine =
  suc
    (four * Program.StaticProgramBitsWidth machine)

programQuotationOverheadExact :
  (machine : Local.ConcreteTapeMachine)
  (stateCoverage :
    Canonical.EnumerationCoverage (Local.finiteState machine))
  (symbolCoverage :
    Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  formulaNodeCount
    (staticProgramDescriptionFormula
      machine stateCoverage symbolCoverage)
  ≡ programQuotationOverhead machine
programQuotationOverheadExact =
  staticProgramDescriptionFormulaNodeCount
