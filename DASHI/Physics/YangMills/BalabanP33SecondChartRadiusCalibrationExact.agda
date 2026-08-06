module DASHI.Physics.YangMills.BalabanP33SecondChartRadiusCalibrationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- A conservative analytic Duhamel estimate of the form
--
--   ||D2 exp_X-D2 exp_0|| <= 6 ||X||
--
-- fits the existing rho/16 diagonal Wilson allocation after shrinking the
-- local chart radius to rho/96.  The exact rational calibration is proved here;
-- the physical Duhamel estimate remains a separately named producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

p33Radius : ℚ
p33Radius = + 1 / 8192

secondChartLipschitzConstant : ℚ
secondChartLipschitzConstant = + 6 / 1

secondChartLocalRadius : ℚ
secondChartLocalRadius = p33Radius * (+ 1 / 96)

secondChartEnvelopeAtLocalRadius : ℚ
secondChartEnvelopeAtLocalRadius =
  secondChartLipschitzConstant * secondChartLocalRadius

secondChartDiagonalAllocation : ℚ
secondChartDiagonalAllocation = p33Radius * (+ 1 / 16)

secondChartEnvelopeFitsDiagonalAllocationExactly :
  secondChartEnvelopeAtLocalRadius ≡ secondChartDiagonalAllocation
secondChartEnvelopeFitsDiagonalAllocationExactly = ℚRing.solve []

record PhysicalSecondChartDefectBound (State : Set) : Set₁ where
  field
    defect normSquared : State → ℚ
    analyticDuhamelBound : ∀ state →
      defect state
      ≤ secondChartEnvelopeAtLocalRadius * normSquared state

open PhysicalSecondChartDefectBound public

secondChartDefectFitsRhoOverSixteen :
  ∀ {State}
    (dataSet : PhysicalSecondChartDefectBound State)
    state →
  defect dataSet state
  ≤ secondChartDiagonalAllocation * normSquared dataSet state
secondChartDefectFitsRhoOverSixteen dataSet state =
  subst
    (λ coefficient →
      defect dataSet state ≤ coefficient * normSquared dataSet state)
    secondChartEnvelopeFitsDiagonalAllocationExactly
    (analyticDuhamelBound dataSet state)

secondChartRadiusCalibrationLevel : ProofLevel
secondChartRadiusCalibrationLevel = machineChecked

physicalSecondDexpDuhamelBoundLevel : ProofLevel
physicalSecondDexpDuhamelBoundLevel = conditional
