module DASHI.Mathematics.Complexity.PNotEqualsNPSATDiagonalRejectedAnchorWidthExact where

------------------------------------------------------------------------
-- REJECTED-ANCHOR WIDTH IN THE ACTUAL SAT-DIAGONAL BODY INTERFACE
--
-- The generic universality audit and the indexed reject-guard owner establish:
--
--   * self-specialization alone imposes no Shannon-width restriction;
--   * on a candidate-rejected quote, SAT polarity is compatible with a body
--     whose guard=false child preserves an arbitrary payload residual family.
--
-- This file attaches that fact to the literal SATDiagonalBody interface.
--
-- IMPORTANT:
-- We do NOT claim that the repository's diagonal body compiler already emits
-- the guarded payload.  The same-object bridge is an explicit field:
--
--   cookIndexed(actual body output)
--     =
--   rejectGuardRoot(cookIndexed(payload)).
--
-- Once that bridge is supplied, arbitrary payload width transfers to the
-- ACTUAL body output and every honest Q1 quotient of that output pays the same
-- per-layer semantic-width lower bound.
--
-- Therefore "candidate rejected this quote" is not itself a small-width law.
-- Any positive Q1 theorem must use a stronger global/all-quotes/resource law.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPKleeneToSelfDiagonalBridgeExact as Diagonal
import DASHI.Mathematics.Complexity.PNotEqualsNPKleeneSpecializationFixedPointExact as Kleene
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfSpecializationWidthUniversalityNoGoExact as Universal
import DASHI.Mathematics.Complexity.PNotEqualsNPRejectGuardResidualWidthEmbeddingExact as Guard
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedRejectGuardCommutationExact as Commute
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact as ArityTerminal

------------------------------------------------------------------------
-- One actual quoted-program body output carrying a width-preserving rejected
-- anchor.
------------------------------------------------------------------------

record RejectedAnchorWidthRealization
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.SpecializingProgramSystem}
    {view : Diagonal.CookFormulaOutputView system}
    {dynamicInput : Kleene.Input system}
    (body :
      Diagonal.SATDiagonalBody
        candidate
        system
        view
        dynamicInput)
    (remaining width : Nat) : Set₁ where
  field
    quoted :
      Kleene.Program system

    payload :
      Cook.BooleanFormula

    quotedRejected :
      Direct.decide
        candidate
        (Diagonal.asFormula view
          (Kleene.run1 system
            quoted
            dynamicInput))
      ≡ false

    payloadWidth :
      Width.ResidualWidthWitness
        {root =
          Family.cookIndexedRestrictionRoot payload}
        remaining
        width

    bodyOutputIsRejectWidthGadget :
      Diagonal.asFormula view
        (Kleene.run2 system
          (Diagonal.bodyProgram body)
          quoted
          dynamicInput)
      ≡
      Universal.rejectWidthGadget payload

open RejectedAnchorWidthRealization public

------------------------------------------------------------------------
-- Because this is a literal SATDiagonalBody and the quote is rejected, its
-- actual body output is satisfiable.  This uses the existing body contract,
-- not any property of the guard gadget.
------------------------------------------------------------------------

rejectedAnchorBodyOutputSatisfiable :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.SpecializingProgramSystem}
    {view : Diagonal.CookFormulaOutputView system}
    {dynamicInput : Kleene.Input system}
    {body :
      Diagonal.SATDiagonalBody
        candidate
        system
        view
        dynamicInput}
    {remaining width : Nat}
    (realization :
      RejectedAnchorWidthRealization body remaining width) →
  Cook.Satisfiable
    (Diagonal.asFormula view
      (Kleene.run2 system
        (Diagonal.bodyProgram body)
        (quoted realization)
        dynamicInput))
rejectedAnchorBodyOutputSatisfiable
    {body = body}
    realization =
  Diagonal.satisfiableIfQuotedProgramRejected
    body
    (quoted realization)
    (quotedRejected realization)

------------------------------------------------------------------------
-- First transport the payload witness into the indexed reject-guard subtree.
------------------------------------------------------------------------

guardedPayloadWidth :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.SpecializingProgramSystem}
    {view : Diagonal.CookFormulaOutputView system}
    {dynamicInput : Kleene.Input system}
    {body :
      Diagonal.SATDiagonalBody
        candidate
        system
        view
        dynamicInput}
    {remaining width : Nat}
    (realization :
      RejectedAnchorWidthRealization body remaining width) →
  Width.ResidualWidthWitness
    {root =
      Guard.rejectGuardRoot
        (Family.cookIndexedRestrictionRoot
          (payload realization))}
    remaining
    width
guardedPayloadWidth realization =
  Guard.rejectGuardPreservesResidualWidthWitness
    (payloadWidth realization)

------------------------------------------------------------------------
-- The representation seam is now derived, not postulated.
--
-- A Cook-level identity of the actual body output with the canonical reject
-- gadget induces equality of the complete dependent indexed views:
--
--   (canonical arity , canonical indexed body)
--     =
--   (suc payload arity , indexed guard root).
------------------------------------------------------------------------

IndexedRoot : Set
IndexedRoot =
  Σ Nat (λ variables → SAT.BooleanFormula variables)

RootResidualWidth :
  Nat →
  Nat →
  IndexedRoot →
  Set₁
RootResidualWidth remaining width (variables , root) =
  Width.ResidualWidthWitness
    {root = root}
    remaining
    width

bodyIndexedViewExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.SpecializingProgramSystem}
    {view : Diagonal.CookFormulaOutputView system}
    {dynamicInput : Kleene.Input system}
    {body :
      Diagonal.SATDiagonalBody
        candidate
        system
        view
        dynamicInput}
    {remaining width : Nat}
    (realization :
      RejectedAnchorWidthRealization body remaining width) →
  Bridge.cookFormulaIndexedView
      (Diagonal.asFormula view
        (Kleene.run2 system
          (Diagonal.bodyProgram body)
          (quoted realization)
          dynamicInput))
  ≡
  ( suc (Bridge.formulaVariableBound
      (payload realization))
  , Guard.rejectGuardRoot
      (Bridge.cookToIndexed
        (payload realization))
  )
bodyIndexedViewExact realization =
  trans
    (cong
      Bridge.cookFormulaIndexedView
      (bodyOutputIsRejectWidthGadget realization))
    (Commute.cookFormulaIndexedViewRejectGuardExact
      (payload realization))

------------------------------------------------------------------------
-- Move the guarded width witness back across that dependent view equality.
------------------------------------------------------------------------

actualBodyOutputWidth :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.SpecializingProgramSystem}
    {view : Diagonal.CookFormulaOutputView system}
    {dynamicInput : Kleene.Input system}
    {body :
      Diagonal.SATDiagonalBody
        candidate
        system
        view
        dynamicInput}
    {remaining width : Nat}
    (realization :
      RejectedAnchorWidthRealization body remaining width) →
  Width.ResidualWidthWitness
    {root =
      Family.cookIndexedRestrictionRoot
        (Diagonal.asFormula view
          (Kleene.run2 system
            (Diagonal.bodyProgram body)
            (quoted realization)
            dynamicInput))}
    remaining
    width
actualBodyOutputWidth
    {remaining = remaining}
    {width = width}
    realization =
  subst
    (RootResidualWidth remaining width)
    (sym
      (bodyIndexedViewExact realization))
    (guardedPayloadWidth realization)

------------------------------------------------------------------------
-- Literal Q1 consequence on the ACTUAL body output.
------------------------------------------------------------------------

rejectedAnchorWidthBelowActualBodyQ1StateCount :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.SpecializingProgramSystem}
    {view : Diagonal.CookFormulaOutputView system}
    {dynamicInput : Kleene.Input system}
    {body :
      Diagonal.SATDiagonalBody
        candidate
        system
        view
        dynamicInput}
    {remaining width : Nat}
    (realization :
      RejectedAnchorWidthRealization body remaining width)
    (quotient :
      Quotient.RestrictionSemanticQuotient
        (Family.cookIndexedRestrictionRoot
          (Diagonal.asFormula view
            (Kleene.run2 system
              (Diagonal.bodyProgram body)
              (quoted realization)
              dynamicInput)))) →
  width ≤ Quotient.stateCount quotient
rejectedAnchorWidthBelowActualBodyQ1StateCount
    realization
    quotient =
  Width.residualWidthBelowQ1StateCount
    quotient
    (actualBodyOutputWidth realization)

------------------------------------------------------------------------
-- Preferred arity-tracked finite-candidate consequence.
--
-- This is the path on which cross-layer state reuse is explicitly forbidden.
------------------------------------------------------------------------

rejectedAnchorWidthBelowArityAdmittedCandidateStateCount :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidateDecider : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.SpecializingProgramSystem}
    {view : Diagonal.CookFormulaOutputView system}
    {dynamicInput : Kleene.Input system}
    {body :
      Diagonal.SATDiagonalBody
        candidateDecider
        system
        view
        dynamicInput}
    {remaining width : Nat}
    (realization :
      RejectedAnchorWidthRealization body remaining width)
    {candidate :
      Candidate.TransitionTableCandidate
        (Family.cookIndexedRestrictionRoot
          (Diagonal.asFormula view
            (Kleene.run2 system
              (Diagonal.bodyProgram body)
              (quoted realization)
              dynamicInput)))} →
  ArityTerminal.ArityTrackedTerminalAdmission candidate →
  width ≤ Candidate.stateCount candidate
rejectedAnchorWidthBelowArityAdmittedCandidateStateCount
    realization
    admission =
  Width.residualWidthBelowArityAdmittedCandidateStateCount
    admission
    (actualBodyOutputWidth realization)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The remaining special-family fork is now sharper:
--
--   rejected quote + local diagonal SAT polarity
--       DOES NOT imply
--   small residual width.
--
-- To rule out width-preserving self-instantiation one must prove that the
-- ACTUAL all-quotes body cannot satisfy bodyOutputIsRejectWidthGadget for a high-width
-- payload family under the charged resource/termination constraints.
--
-- Conversely, any construction of this equality for a high-width payload
-- immediately transfers that width into the actual body-output Q1 quotient.
------------------------------------------------------------------------
