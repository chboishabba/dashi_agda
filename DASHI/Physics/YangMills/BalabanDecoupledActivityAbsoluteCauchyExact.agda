module DASHI.Physics.YangMills.BalabanDecoupledActivityAbsoluteCauchyExact where

-- Absolute Cauchy lift for the literal CMP116 decoupled activity.
--
-- `BalabanDecoupledActivityHessian` already constructs the source-shaped
-- coefficient of the twice-varied local activity in the finite decoupling
-- parameters.  Its historical Cauchy theorem controls DIFFERENCES of two such
-- coefficients.  Canonical B/P0 instead needs an ABSOLUTE localization bound
-- for one selected coefficient.
--
-- This file proves exactly that missing generic step.  The only application
-- input left is the genuine CMP116 boundary estimate on the same decoupled
-- activity.  No domain comparison, Hessian sensitivity, marked-walk replay,
-- Heat/Doob or Langevin object is introduced.

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
import DASHI.Foundations.FinitePolydiscCauchyAbsoluteAxioms as Absolute
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled

absoluteBoundaryComparisonLiftsToCoefficient :
  (D : Decoupled.DecoupledActivityHessianData) →
  (A : Absolute.FinitePolydiscCauchyAbsoluteAxioms (Decoupled.cauchy D)) →
  (Ω : Decoupled.DomainSequence D) →
  (Y : Decoupled.Component D) →
  (u v : Decoupled.FieldVariation D) →
  (M : ℝ) →
  Absolute.BoundaryValueBound A (Decoupled.asFunction D Ω Y u v) M →
  Cauchy.normValue (Decoupled.cauchy D)
    (Decoupled.decoupledHessianCoefficient D Ω Y u v)
  ≤ℝ M
absoluteBoundaryComparisonLiftsToCoefficient D A Ω Y u v M boundary =
  Absolute.coefficientAbsoluteBound A
    (Decoupled.asFunction D Ω Y u v) M boundary

-- Pointwise boundary control is the form CMP116 produces after the generalized
-- random-walk/decoupling estimates.  This theorem constructs the absolute
-- boundary witness and immediately obtains the finite-polydisc coefficient
-- estimate.
pointwiseAbsoluteBoundaryLiftsToCoefficient :
  (D : Decoupled.DecoupledActivityHessianData) →
  (A : Absolute.FinitePolydiscCauchyAbsoluteAxioms (Decoupled.cauchy D)) →
  (Ω : Decoupled.DomainSequence D) →
  (Y : Decoupled.Component D) →
  (u v : Decoupled.FieldVariation D) →
  (M : ℝ) →
  (∀ (s : Cauchy.BoundaryAssignment
      (Decoupled.cauchy D) (Decoupled.componentIndices D Y)) →
    Cauchy.normValue (Decoupled.cauchy D)
      (Cauchy.evaluate (Decoupled.cauchy D)
        (Decoupled.asFunction D Ω Y u v)
        (Cauchy.boundaryAssignment (Decoupled.cauchy D) s))
    ≤ℝ M) →
  Cauchy.normValue (Decoupled.cauchy D)
    (Decoupled.decoupledHessianCoefficient D Ω Y u v)
  ≤ℝ M
pointwiseAbsoluteBoundaryLiftsToCoefficient D A Ω Y u v M pointwise =
  absoluteBoundaryComparisonLiftsToCoefficient D A Ω Y u v M
    (Absolute.boundaryValueEnvelope A
      (Decoupled.asFunction D Ω Y u v) M pointwise)

-- Critical-path interpretation:
--
--   pointwise absolute localization of the CMP116 boundary integrand
--       -> finite-polydisc Cauchy coefficient
--       -> absolute localized twice-varied activity coefficient.
--
-- Therefore comparison-only data are not required for the absolute B route.
