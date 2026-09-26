module DASHI.Mathematics.Complexity.PNotEqualsNPSelfSpecializationWidthUniversalityNoGoExact where

------------------------------------------------------------------------
-- GENERIC SELF-SPECIALIZATION DOES NOT FORCE SMALL SHANNON WIDTH
--
-- Candidate structural hope under audit:
--
--   perhaps being produced by the finite Kleene/self-specializing calculus
--   already forces a special restricted family of Boolean formulas.
--
-- This is false for the generic calculus.
--
-- One fixed primitive semantics can ignore the quoted program and return its
-- dynamic Cook-formula input unchanged.  The ONE literal fixed-point program
--
--   primitiveBodyFixedPoint echoInput
--
-- then evaluates to every Cook Boolean formula as the dynamic input varies.
--
-- Therefore the generic self-specialization syntax is surjective onto ordinary
-- Cook formula syntax.  Any residual-width restriction used by Q1 must come
-- from stronger properties of the SPECIFIC SAT-diagonal primitive semantics,
-- not from Kleene specialization/diagonalization itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Agda.Builtin.Nat using (Nat)
open import Data.Maybe.Base using (just)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Finite
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPKleeneToSelfDiagonalBridgeExact as Diagonal
import DASHI.Mathematics.Complexity.PNotEqualsNPKleeneSpecializationFixedPointExact as TotalKleene
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family

------------------------------------------------------------------------
-- One fixed primitive instruction.
------------------------------------------------------------------------

data EchoPrimitive : Set where
  echoInput : EchoPrimitive

------------------------------------------------------------------------
-- One fixed semantics:
--
--   run1 echo x   = x
--   run2 echo q x = x
--
-- The quoted program is intentionally ignored.  This is a valid inhabitant of
-- the generic finite-code interface and demonstrates that self-specialization
-- alone imposes no output-language restriction.
------------------------------------------------------------------------

echoFormulaSemantics :
  Finite.PrimitiveSemantics
    EchoPrimitive
    Cook.BooleanFormula
    Cook.BooleanFormula
echoFormulaSemantics = record
  { Finite.runPrimitive1 =
      λ primitive input →
        just input
  ; Finite.runPrimitive2 =
      λ primitive quoted input →
        just input
  }

------------------------------------------------------------------------
-- One literal self-specializing fixed-point program.
------------------------------------------------------------------------

echoFixedPointProgram :
  Finite.Program EchoPrimitive
echoFixedPointProgram =
  Finite.primitiveBodyFixedPoint echoInput

------------------------------------------------------------------------
-- Main universality theorem.
------------------------------------------------------------------------

echoFixedPointOutputsEveryFormula :
  (formula : Cook.BooleanFormula) →
  Finite.run1
    echoFormulaSemantics
    echoFixedPointProgram
    formula
  ≡
  just formula
echoFixedPointOutputsEveryFormula formula =
  refl

------------------------------------------------------------------------
-- The exact indexed Shannon root of every formula is therefore obtainable as
-- the restriction root of a literal output of the same self-specializing
-- fixed-point program.
------------------------------------------------------------------------

echoFixedPointRestrictionRoot :
  (formula : Cook.BooleanFormula) →
  Family.cookIndexedRestrictionRoot formula
  ≡
  Family.cookIndexedRestrictionRoot formula
echoFixedPointRestrictionRoot formula =
  refl

echoFixedPointRestrictionRootRoundTrip :
  (formula : Cook.BooleanFormula) →
  Bridge.indexedToCook
    (Family.cookIndexedRestrictionRoot formula)
  ≡
  formula
echoFixedPointRestrictionRootRoundTrip =
  Family.cookRestrictionRootRoundTrip

------------------------------------------------------------------------
-- Explicit image receipt for the one fixed-point program.
------------------------------------------------------------------------

record EchoFixedPointImage
    (formula : Cook.BooleanFormula) : Set where
  constructor echo-fixed-point-image
  field
    dynamicInput :
      Cook.BooleanFormula

    execution :
      Finite.run1
        echoFormulaSemantics
        echoFixedPointProgram
        dynamicInput
      ≡
      just formula

open EchoFixedPointImage public

everyFormulaIsInEchoFixedPointImage :
  (formula : Cook.BooleanFormula) →
  EchoFixedPointImage formula
everyFormulaIsInEchoFixedPointImage formula =
  echo-fixed-point-image
    formula
    refl

------------------------------------------------------------------------
-- Width transport is literal: self-specialization does not shrink the Shannon
-- residual family because the fixed-point output is the payload formula itself.
------------------------------------------------------------------------

record EchoFixedPointResidualWidth
    (remaining width : Nat) : Set₁ where
  constructor echo-fixed-point-residual-width
  field
    formula :
      Cook.BooleanFormula

    image :
      EchoFixedPointImage formula

    widthWitness :
      Width.ResidualWidthWitness
        {root = Family.cookIndexedRestrictionRoot formula}
        remaining
        width

open EchoFixedPointResidualWidth public

anyResidualWidthOccursInEchoFixedPointImage :
  ∀ {remaining width}
    (formula : Cook.BooleanFormula) →
  Width.ResidualWidthWitness
    {root = Family.cookIndexedRestrictionRoot formula}
    remaining
    width →
  EchoFixedPointResidualWidth remaining width
anyResidualWidthOccursInEchoFixedPointImage
    formula
    witness =
  echo-fixed-point-residual-width
    formula
    (everyFormulaIsInEchoFixedPointImage formula)
    witness

------------------------------------------------------------------------
-- Specific SAT-diagonal body: literal payload passthrough is blocked.
--
-- Suppose one quoted program evaluates to the known satisfiable anchor and the
-- diagonal body returns literally that same formula.  The body obligation
--
--   body satisfiable -> candidate rejects quoted output
--
-- then contradicts the anchored candidate's acceptance of that formula.
--
-- Therefore the generic echo/passthrough universality above cannot simply be
-- reused as the actual SAT-diagonal primitive body.
------------------------------------------------------------------------

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

literalPassthroughAtKnownSatisfiableImpossible :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {anchored : Direct.AnchoredPolynomialSATDeciderCandidate cost}
    {system : TotalKleene.SpecializingProgramSystem}
    {view : Diagonal.CookFormulaOutputView system}
    {dynamicInput : TotalKleene.Input system}
    (body :
      Diagonal.SATDiagonalBody
        (Direct.candidate anchored)
        system
        view
        dynamicInput)
    (quoted : TotalKleene.Program system) →
  Diagonal.asFormula view
      (TotalKleene.run1 system quoted dynamicInput)
    ≡
    Cook.excludedMiddleFormula →
  Diagonal.asFormula view
      (TotalKleene.run2
        system
        (Diagonal.bodyProgram body)
        quoted
        dynamicInput)
    ≡
    Diagonal.asFormula view
      (TotalKleene.run1 system quoted dynamicInput) →
  ⊥
literalPassthroughAtKnownSatisfiableImpossible
    {anchored = anchored}
    {system = system}
    {view = view}
    {dynamicInput = dynamicInput}
    body
    quoted
    quotedIsKnownSat
    bodyIsQuoted =
  trueNotFalse contradiction
  where
    quotedFormula :
      Cook.BooleanFormula
    quotedFormula =
      Diagonal.asFormula view
        (TotalKleene.run1 system quoted dynamicInput)

    bodyFormula :
      Cook.BooleanFormula
    bodyFormula =
      Diagonal.asFormula view
        (TotalKleene.run2
          system
          (Diagonal.bodyProgram body)
          quoted
          dynamicInput)

    quotedSatisfiable :
      Cook.Satisfiable quotedFormula
    quotedSatisfiable =
      subst
        Cook.Satisfiable
        (sym quotedIsKnownSat)
        Cook.excludedMiddleFormulaIsSatisfiable

    bodySatisfiable :
      Cook.Satisfiable bodyFormula
    bodySatisfiable =
      subst
        Cook.Satisfiable
        (sym bodyIsQuoted)
        quotedSatisfiable

    candidateRejectsQuoted :
      Direct.decide
        (Direct.candidate anchored)
        quotedFormula
      ≡
      false
    candidateRejectsQuoted =
      Diagonal.rejectsQuotedProgramIfBodySatisfiable
        body
        quoted
        bodySatisfiable

    candidateDecisionTransport :
      Direct.decide
        (Direct.candidate anchored)
        quotedFormula
      ≡
      Direct.decide
        (Direct.candidate anchored)
        Cook.excludedMiddleFormula
    candidateDecisionTransport =
      cong
        (Direct.decide
          (Direct.candidate anchored))
        quotedIsKnownSat

    contradiction :
      true
      ≡
      false
    contradiction =
      trans
        (sym
          (Direct.acceptsKnownSatisfiable anchored))
        (trans
          (sym candidateDecisionTransport)
          candidateRejectsQuoted)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The universality fork is partly resolved:
--
--   generic self-specialization
--     DOES NOT
--   imply small FutureEquivalent / residual-function width.
--
-- The fixed-point machinery can emit arbitrary formula syntax.
--
-- Hence a positive Q1 width theorem must use a law of the actual SAT-diagonal
-- primitive body / candidate interaction which is absent from this echo model.
--
-- The remaining high-alpha falsification question is narrower:
--
--   does the SPECIFIC SAT-diagonal body still admit a width-preserving payload
--   embedding, or does its candidate/rejection semantics forbid one?
------------------------------------------------------------------------
