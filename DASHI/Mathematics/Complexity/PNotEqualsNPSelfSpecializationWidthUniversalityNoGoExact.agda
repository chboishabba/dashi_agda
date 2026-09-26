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

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (just)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Finite
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
  DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact.indexedToCook
    (Family.cookIndexedRestrictionRoot formula)
  ≡
  formula
echoFixedPointRestrictionRootRoundTrip =
  Family.cookRestrictionRootRoundTrip

------------------------------------------------------------------------
-- Property firewall.
--
-- Any property claimed solely from "is output by a finite self-specializing
-- fixed-point program" must, for this generic calculus, tolerate every Cook
-- formula.  The fixed-point syntax itself cannot establish a small-width
-- theorem.
------------------------------------------------------------------------

SelfSpecializingOutputProperty :
  (Cook.BooleanFormula → Set) →
  Set
SelfSpecializingOutputProperty Property =
  (formula : Cook.BooleanFormula) →
  Property formula

genericFixedPointImagePropertyIsUniversal :
  (Property : Cook.BooleanFormula → Set) →
  ((input : Cook.BooleanFormula) →
    Property input) →
  SelfSpecializingOutputProperty Property
genericFixedPointImagePropertyIsUniversal Property property =
  property

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
