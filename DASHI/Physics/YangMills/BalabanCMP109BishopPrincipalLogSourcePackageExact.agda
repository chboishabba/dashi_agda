module DASHI.Physics.YangMills.BalabanCMP109BishopPrincipalLogSourcePackageExact where

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
-- Assemble the two quantitative principal-log facts that were previously
-- separated across the Bishop lane:
--
--   * on the full constructive half ball, the symmetric inverse-dexp plane
--     coefficient is at least 23/24;
--   * at the literal CMP109 source radius 1/12, the Bernoulli coefficient
--     satisfies 0 <= beta-1/12 <= 1/14400.
--
-- The constructor below derives the package from the actual Bishop series
-- inputs.  No rational surrogate for beta is accepted.  What remains of the
-- former `LiteralSU2PrincipalLogProductFrechetExact` leaf is therefore the
-- same-object map/trivialization bridge into the printed CMP109 derivative,
-- not a missing scalar principal-log estimate.
------------------------------------------------------------------------

import Real as BishopReal
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpPositiveDenominatorExact as Positive
import DASHI.Physics.YangMills.BalabanCMP109BishopPrincipalLogSymmetricCoefficientExact as Symmetric
import DASHI.Physics.YangMills.BalabanCMP109BishopInverseDexpCoefficientEndpointModulusExact as Endpoint
import DASHI.Physics.YangMills.BalabanCMP109BishopSourceRadiusEndpointExact as Source
open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP109BishopPrincipalLogSourcePackage
    {dataSet}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs
      dataSet Source.sourceRadiusValue) : Set where
  field
    endpointDefectNonnegative :
      BishopReal._≤_ BishopReal.0ℝ
        (Endpoint.coefficientEndpointDefect
          inputs Source.sourceRadiusPositive)

    endpointDefectBelowOne14400 :
      BishopReal._≤_
        (Endpoint.coefficientEndpointDefect
          inputs Source.sourceRadiusPositive)
        (Source.embed Source.sourceEndpointAllowance)

    symmetricCoefficientAboveTwentyThreeTwentyFourth :
      BishopReal._≤_
        (Symmetric.embed Symmetric.twentyThreeTwentyFourth)
        (Symmetric.principalLogSymmetricCoefficient
          inputs (Positive.positiveRadius Source.sourceRadiusPositive))

open CMP109BishopPrincipalLogSourcePackage public

cmp109BishopPrincipalLogSourcePackage :
  ∀ {dataSet}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs
      dataSet Source.sourceRadiusValue) →
  CMP109BishopPrincipalLogSourcePackage inputs
cmp109BishopPrincipalLogSourcePackage inputs = record
  { endpointDefectNonnegative =
      Source.sourceRadiusCoefficientEndpointNonnegative inputs
  ; endpointDefectBelowOne14400 =
      Source.sourceRadiusCoefficientEndpointModulus inputs
  ; symmetricCoefficientAboveTwentyThreeTwentyFourth =
      Symmetric.principalLogSymmetricCoefficientAboveTwentyThreeTwentyFourth
        inputs (Positive.positiveRadius Source.sourceRadiusPositive)
  }

cmp109BishopPrincipalLogSourceQuantitativePackageLevel : ProofLevel
cmp109BishopPrincipalLogSourceQuantitativePackageLevel = machineChecked

cmp109PrintedPrincipalLogSameObjectTrivializationLevel : ProofLevel
cmp109PrintedPrincipalLogSameObjectTrivializationLevel = conditional
