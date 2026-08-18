module DASHI.Physics.YangMills.BalabanCMP109BishopSourceRadiusEndpointExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Specialize the already checked Bishop inverse-dexp endpoint modulus to the
-- literal CMP109 source radius t=1/12.  The generic theorem gives
--
--   0 <= beta(t)-1/12 <= t^2/100.
--
-- At t=1/12 the upper endpoint is exactly 1/14400.  This was previously only
-- recorded as a rational target in PrincipalLogSourceRadiusDefectExact.  Here
-- it is proved on the actual Bishop coefficient, without replacing beta by a
-- rational approximation.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanCMP109BishopInverseDexpCoefficientEndpointModulusExact as Endpoint
open import DASHI.Physics.YangMills.CompactLieProofLevel

sourceRadius sourceEndpointAllowance : ℚᵘ
sourceRadius = + 1 / 12
sourceEndpointAllowance = + 1 / 14400

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

sourceRadiusValue : BishopReal.ℝ
sourceRadiusValue = embed sourceRadius

sourceQuadraticScaleIsAllowance :
  BishopReal._≃_
    (BishopReal._*_
      (embed Endpoint.oneHundred)
      (Endpoint.square sourceRadiusValue))
    (embed sourceEndpointAllowance)
sourceQuadraticScaleIsAllowance =
  let open BishopProperties.ℝ-Solver
  in solve 0
    ((Κ (+ 1 / 100) ⊗ (Κ (+ 1 / 12) ⊗ Κ (+ 1 / 12)))
      ⊜ Κ (+ 1 / 14400))
    BishopProperties.≃-refl

sourceRadiusCoefficientEndpointModulus :
  ∀ {dataSet}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet sourceRadiusValue)
    (sourceRadiusPositive :
      BishopReal._<_ BishopReal.0ℝ sourceRadiusValue) →
  BishopReal._≤_
    (Endpoint.coefficientEndpointDefect inputs sourceRadiusPositive)
    (embed sourceEndpointAllowance)
sourceRadiusCoefficientEndpointModulus inputs sourceRadiusPositive =
  BishopProperties.≤-respʳ-≃
    sourceQuadraticScaleIsAllowance
    (Endpoint.defectQuadraticUpper
      (Endpoint.positiveCoefficientEndpointModulus
        inputs sourceRadiusPositive))

sourceRadiusCoefficientEndpointNonnegative :
  ∀ {dataSet}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet sourceRadiusValue)
    (sourceRadiusPositive :
      BishopReal._<_ BishopReal.0ℝ sourceRadiusValue) →
  BishopReal._≤_ BishopReal.0ℝ
    (Endpoint.coefficientEndpointDefect inputs sourceRadiusPositive)
sourceRadiusCoefficientEndpointNonnegative inputs sourceRadiusPositive =
  Endpoint.defectNonnegative
    (Endpoint.positiveCoefficientEndpointModulus inputs sourceRadiusPositive)

cmp109BishopSourceRadiusOne14400Level : ProofLevel
cmp109BishopSourceRadiusOne14400Level = machineChecked

-- Remaining same-object seam: transport the Bishop-real beta(Y) itself into
-- the finite matrix coefficient used for the printed CMP109 derivative.  The
-- numerical endpoint allowance is no longer missing.
cmp109BishopCoefficientToPrintedMatrixSameObjectLevel : ProofLevel
cmp109BishopCoefficientToPrintedMatrixSameObjectLevel = conditional
