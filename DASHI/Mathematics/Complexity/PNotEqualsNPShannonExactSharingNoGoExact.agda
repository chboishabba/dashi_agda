module DASHI.Mathematics.Complexity.PNotEqualsNPShannonExactSharingNoGoExact where

------------------------------------------------------------------------
-- SHANNON TREE EXACT-SUBFORMULA SHARING NO-GO
--
-- PNotEqualsNPSATShannonSemanticAuthorityExact gives a genuine SAT-specific
-- semantic factorization but its full expansion has 2^n leaves.
--
-- Could exact DAG sharing collapse those leaves generically?
--
-- No.  This owner constructs an n-variable "assignment signature" formula
-- whose complete restrictions along distinct assignments are syntactically
-- distinct zero-variable formulas.
--
-- Therefore the full Shannon tree can contain 2^n pairwise distinct terminal
-- subinstances even for a tiny recursively generated formula family.
--
-- This does not rule out deeper semantic sharing; it rules out generic sharing
-- by exact equality of restricted formulas.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base as Fin using (zero)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSATSelfReductionUnusedVariableNoGoExact as Weaken
import DASHI.Mathematics.Complexity.PNotEqualsNPSATSelfReductionTerminalSizeNoGoExact as Terminal
import DASHI.Mathematics.Complexity.PNotEqualsNPSATSelfReductionSizeNoGoExact as Size

------------------------------------------------------------------------
-- Recursively generated formula carrying one syntactic occurrence of every
-- variable.  The tail is weakened so the new head variable occupies index 0.
------------------------------------------------------------------------

signatureFormula :
  (variables : Nat) →
  SAT.BooleanFormula variables
signatureFormula zero =
  SAT.constant false
signatureFormula (suc variables) =
  SAT.conjunction
    (SAT.variable Fin.zero)
    (Weaken.weakenFormula
      (signatureFormula variables))

------------------------------------------------------------------------
-- Complete restriction records the assignment bits as constant leaves.
------------------------------------------------------------------------

decodeSignature :
  (variables : Nat) →
  SAT.BooleanFormula zero →
  Maybe (Vec Bool variables)
decodeSignature zero (SAT.constant false) =
  just []
decodeSignature zero formula =
  nothing
decodeSignature (suc variables)
    (SAT.conjunction (SAT.constant bit) rest)
    with decodeSignature variables rest
... | just bits =
  just (bit ∷ bits)
... | nothing =
  nothing
decodeSignature (suc variables) formula =
  nothing

decodeFullyRestrictedSignature :
  ∀ {variables : Nat}
    (bits : Vec Bool variables) →
  decodeSignature
    variables
    (Terminal.fullyRestrict
      bits
      (signatureFormula variables))
  ≡ just bits
decodeFullyRestrictedSignature {zero} [] =
  refl
decodeFullyRestrictedSignature {suc variables}
    (false ∷ bits)
    rewrite
      Weaken.restrictWeakenFalse
        (signatureFormula variables)
      |
      decodeFullyRestrictedSignature bits =
  refl
decodeFullyRestrictedSignature {suc variables}
    (true ∷ bits)
    rewrite
      Weaken.restrictWeakenTrue
        (signatureFormula variables)
      |
      decodeFullyRestrictedSignature bits =
  refl

------------------------------------------------------------------------
-- Distinct assignments produce distinct terminal formulas.
------------------------------------------------------------------------

justInjective :
  ∀ {A : Set}
    {left right : A} →
  just left ≡ just right →
  left ≡ right
justInjective refl =
  refl

fullyRestrictedSignatureInjective :
  ∀ {variables : Nat}
    {left right : Vec Bool variables} →
  Terminal.fullyRestrict
    left
    (signatureFormula variables)
  ≡
  Terminal.fullyRestrict
    right
    (signatureFormula variables) →
  left ≡ right
fullyRestrictedSignatureInjective
    {variables} {left} {right} same =
  justInjective
    (trans
      (sym
        (decodeFullyRestrictedSignature left))
      (trans
        (cong
          (decodeSignature variables)
          same)
        (decodeFullyRestrictedSignature right)))

------------------------------------------------------------------------
-- All terminal instances also retain the original formula's node count.
------------------------------------------------------------------------

fullyRestrictedSignaturePreservesNodeCount :
  ∀ {variables : Nat}
    (bits : Vec Bool variables) →
  Size.formulaNodeCount
    (Terminal.fullyRestrict
      bits
      (signatureFormula variables))
  ≡
  Size.formulaNodeCount
    (signatureFormula variables)
fullyRestrictedSignaturePreservesNodeCount
    {variables} bits =
  Terminal.fullyRestrictPreservesNodeCount
    bits
    (signatureFormula variables)

------------------------------------------------------------------------
-- Research consequence.
--
-- Even after moving from raw computation trajectories to the exact SAT
-- Shannon semantic law, exact subformula sharing cannot generically collapse
-- the 2^n restriction tree: this family has one distinct terminal formula per
-- assignment, all at the same syntax-node count under the repository's literal
-- restriction representation.
--
-- Any useful compression of Shannon authority therefore has to identify a
-- deeper semantic equivalence/invariant, not repeated exact restricted syntax.
------------------------------------------------------------------------
