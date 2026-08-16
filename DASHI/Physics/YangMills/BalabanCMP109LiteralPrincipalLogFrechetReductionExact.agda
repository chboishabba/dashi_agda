module DASHI.Physics.YangMills.BalabanCMP109LiteralPrincipalLogFrechetReductionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Shrink the remaining G1 source-calculus seam.  The physical equation-(0.11)
-- differential previously asked directly for both printed component formulas
--
--   D_U log(U_j V^-1)[u_j] = J_+(Y_j) u_j,
--   D_V log(U_j V^-1)[v]   = - J_+(Y_j) Ad_{exp Y_j} v.
--
-- Round 54 proved J_+ Ad_exp = J_- from the left/right dexp inverse laws.
-- This module therefore makes the centre formula a CONSEQUENCE: callers only
-- identify the two literal one-leg principal-log Frechet derivatives with
-- J_+ and J_- respectively.  The printed J_+ Ad_exp centre formula is then
-- derived from the already-proved action cancellation.
--
-- The remaining analytic leaf is now exactly the source theorem
--
--   D_X log(exp X exp Y)|_0 = J_+(Y),
--   D_X log(exp Y exp X)|_0 = J_-(Y),
--
-- in the literal CMP98/CMP109 chart/trivialisation and Bishop-real carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (0ℚ; _-_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109PhysicalFederbushDifferentiatedEquation011Exact as Printed
import DASHI.Physics.YangMills.BalabanCMP109FiniteMatrixLeftRightDexpCancellationExact as LR

record LiteralPrincipalLogOneLegFrechetData (Index : Set) : Set₁ where
  field
    indices : List Index

    rightInverseDexp : Index → Jacobian.Lie3Matrix
    adjointTransport : Index → Jacobian.Lie3Matrix
    leftInverseDexp : Index → Jacobian.Lie3Matrix

    inputVariation : Index → Jacobian.Lie3Vector
    centreVariation : Jacobian.Lie3Vector

    -- These are the two source-facing analytic facts.  They identify the
    -- actual one-leg derivatives, not a preassembled J*T target.
    actualRightLegDerivative : Index → Jacobian.Lie3Vector
    actualLeftLegDerivative : Index → Jacobian.Lie3Vector

    actualRightLegFrechet : ∀ index row →
      actualRightLegDerivative index row
      ≡ Printed.applyMatrix (rightInverseDexp index) (inputVariation index) row

    actualLeftLegFrechet : ∀ index row →
      actualLeftLegDerivative index row
      ≡ Printed.applyMatrix (leftInverseDexp index) centreVariation row

    leftRightDexpData : ∀ index →
      LR.MatrixLeftRightDexpCancellationData
        (rightInverseDexp index)
        (adjointTransport index)
        (leftInverseDexp index)

open LiteralPrincipalLogOneLegFrechetData public

centreCompositionEqualsLeftInverseDexp :
  ∀ {Index} (data : LiteralPrincipalLogOneLegFrechetData Index)
    index row column →
  Printed.composeMatrix
    (rightInverseDexp data index)
    (adjointTransport data index)
    row column
  ≡ leftInverseDexp data index row column
centreCompositionEqualsLeftInverseDexp data index =
  LR.leftRightDexpMatrixCancellation (leftRightDexpData data index)

centreCompositionActionEqualsLeftAction :
  ∀ {Index} (data : LiteralPrincipalLogOneLegFrechetData Index)
    index vector row →
  Printed.applyMatrix
    (Printed.composeMatrix
      (rightInverseDexp data index)
      (adjointTransport data index))
    vector row
  ≡ Printed.applyMatrix (leftInverseDexp data index) vector row
centreCompositionActionEqualsLeftAction data index =
  LR.leftRightDexpActionCancellation (leftRightDexpData data index)

printedCentreDerivativeFromOppositeTrivialization :
  ∀ {Index} (data : LiteralPrincipalLogOneLegFrechetData Index)
    index row →
  0ℚ - actualLeftLegDerivative data index row
  ≡ 0ℚ - Printed.applyMatrix
      (Printed.composeMatrix
        (rightInverseDexp data index)
        (adjointTransport data index))
      (centreVariation data) row
printedCentreDerivativeFromOppositeTrivialization data index row =
  trans
    (cong (0ℚ -_) (actualLeftLegFrechet data index row))
    (cong (0ℚ -_)
      (sym (centreCompositionActionEqualsLeftAction
        data index (centreVariation data) row)))

asPhysicalFederbushEquation011Differential :
  ∀ {Index} → LiteralPrincipalLogOneLegFrechetData Index →
  Printed.PhysicalFederbushEquation011Differential Index
asPhysicalFederbushEquation011Differential data = record
  { Printed.PhysicalFederbushEquation011Differential.indices = indices data
  ; Printed.PhysicalFederbushEquation011Differential.principalLogJacobian =
      rightInverseDexp data
  ; Printed.PhysicalFederbushEquation011Differential.centreTransport =
      adjointTransport data
  ; Printed.PhysicalFederbushEquation011Differential.inputVariation =
      inputVariation data
  ; Printed.PhysicalFederbushEquation011Differential.averageVariation =
      centreVariation data
  ; Printed.PhysicalFederbushEquation011Differential.printedInputDerivative =
      actualRightLegDerivative data
  ; Printed.PhysicalFederbushEquation011Differential.printedCentreDerivative =
      λ index row → 0ℚ - actualLeftLegDerivative data index row
  ; Printed.PhysicalFederbushEquation011Differential.printedInputDerivativeExact =
      actualRightLegFrechet data
  ; Printed.PhysicalFederbushEquation011Differential.printedCentreDerivativeExact =
      printedCentreDerivativeFromOppositeTrivialization data
  }

cmp109LiteralOneLegFrechetReductionLevel : ProofLevel
cmp109LiteralOneLegFrechetReductionLevel = machineChecked

cmp109LiteralPrincipalLogFrechetAnalyticInputsLevel : ProofLevel
cmp109LiteralPrincipalLogFrechetAnalyticInputsLevel = conditional
