module DASHI.Analysis.DashiWeilExactIdentification where

-- Exact identification of a DASHI quadratic with the arithmetic side of the
-- Riemann explicit formula, followed by constructive transport to the
-- spectral side.  The composition lemmas below are proved, not postulated.

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula

record DashiWeilQuadratic
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    DashiTest : Set
    dashiQuadratic : DashiTest → Scalar
    embed : DashiTest → Test

    embeddedAdmissible :
      (x : DashiTest) → admissible (embed x)

    dashiArithmeticAgreement :
      (x : DashiTest) →
      dashiQuadratic x ≡ arithmeticForm (embed x)

    dashiCoercive :
      (x : DashiTest) → nonnegative (dashiQuadratic x)

dashiSpectralAgreement :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (bridge : DashiWeilQuadratic space formula) →
  (x : DashiWeilQuadratic.DashiTest bridge) →
  DashiWeilQuadratic.dashiQuadratic bridge x
  ≡
  RiemannExplicitFormula.spectralZeroForm formula
    (DashiWeilQuadratic.embed bridge x)
dashiSpectralAgreement space formula bridge x =
  ≡-trans
    (DashiWeilQuadratic.dashiArithmeticAgreement bridge x)
    (RiemannExplicitFormula.explicitFormula formula
      (DashiWeilQuadratic.embed bridge x)
      (DashiWeilQuadratic.embeddedAdmissible bridge x))

embeddedSpectralPositive :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (bridge : DashiWeilQuadratic space formula) →
  (x : DashiWeilQuadratic.DashiTest bridge) →
  WeilTestSpace.nonnegative space
    (RiemannExplicitFormula.spectralZeroForm formula
      (DashiWeilQuadratic.embed bridge x))
embeddedSpectralPositive space formula bridge x =
  WeilTestSpace.nonnegativeTransport space
    (dashiSpectralAgreement space formula bridge x)
    (DashiWeilQuadratic.dashiCoercive bridge x)
