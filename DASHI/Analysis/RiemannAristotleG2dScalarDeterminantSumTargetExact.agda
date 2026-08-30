module DASHI.Analysis.RiemannAristotleG2dScalarDeterminantSumTargetExact where

------------------------------------------------------------------------
-- G2d / FINAL BIDI ANALYTIC LEAF
--
-- After G2c the post-Schur quotient is one-dimensional.  Writing
--
--   d_sigma = det(n1,n2,k_sigma),   W = wedgeSq(n1,n2) > 0,
--
-- the finite near energy is controlled by the single signed scalar sum
--
--   (sum_sigma d_sigma)^2 / W.
--
-- Equivalently the Gram debt is
--
--   ((sum d)^2 - sum d^2) / W.
--
-- Reflection pairing alone cannot make this small: the stored paired cells are
-- reflection invariant.  The genuine remaining theorem must therefore provide
-- additional ordinate/phase cancellation for the scalar determinant responses.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record G2dScalarDeterminantSumTarget : Set where
  constructor g2d-scalar-determinant-sum-target
  field
    scalarResponseName : String
    scalarResponseDefinition : String
    exactFiniteEnergyReading : String
    exactGramDebtReading : String
    requiredAnalyticEstimate : String

    vectorGramGeometryRemaining : Bool
    vectorGramGeometryRemainingIsFalse : vectorGramGeometryRemaining ≡ false

    reflectionOnlyCancellationSuffices : Bool
    reflectionOnlyCancellationSufficesIsFalse : reflectionOnlyCancellationSuffices ≡ false

    additionalOrdinatePhaseCancellationRequired : Bool
    additionalOrdinatePhaseCancellationRequiredIsTrue :
      additionalOrdinatePhaseCancellationRequired ≡ true

    signedScalarDeterminantSumBoundClosed : Bool
    signedScalarDeterminantSumBoundClosedIsFalse :
      signedScalarDeterminantSumBoundClosed ≡ false

open G2dScalarDeterminantSumTarget public

canonicalG2dScalarDeterminantSumTarget : G2dScalarDeterminantSumTarget
canonicalG2dScalarDeterminantSumTarget =
  g2d-scalar-determinant-sum-target
    "d_sigma"
    "d_sigma = det3(n1,n2,k_sigma), where k_sigma is the literal reflection-paired three-taper near-cell response"
    "finite post-Schur near energy = (sum_sigma d_sigma)^2 / wedgeSq(n1,n2)"
    "GramDebt = ((sum_sigma d_sigma)^2 - sum_sigma d_sigma^2) / wedgeSq(n1,n2)"
    "prove a signed ordinate/phase cancellation bound on sum_sigma d_sigma strong enough, together with the explicit far error, to lie below the surviving cluster determinant margin"
    false refl
    false refl
    true refl
    false refl
