module DASHI.Physics.YangMills.BalabanP33CMP109LocalLeafCalibrationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
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
-- Calibrate every scalar leaf in the literal four-stage CMP109 allocation.
-- The physical operator estimates still have to identify their concrete
-- derivatives with these leaves, but no radius or multiplicity is left free:
--
--   outer:      2 (rho/16)       = rho/8,
--   logarithm:  t/2+t^2/6 at t=rho/96 < rho/8,
--   transport:  24 (rho/96)      = rho/4,
--   path:       24 (rho/48)      = rho/2.
--
-- The four allocations total rho exactly.  The logarithm leaf reuses the
-- inverse-dexp envelope rather than introducing an independent principal-log
-- normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

rho : ℚ
rho = + 1 / 8192

outerChartRadius logarithmChartRadius : ℚ
outerChartRadius = rho * (+ 1 / 16)
logarithmChartRadius = rho * (+ 1 / 96)

transportStepRadius pathStepRadius : ℚ
transportStepRadius = rho * (+ 1 / 96)
pathStepRadius = rho * (+ 1 / 48)

outerAllocation logarithmAllocation transportAllocation pathAllocation : ℚ
outerAllocation = rho * (+ 1 / 8)
logarithmAllocation = rho * (+ 1 / 8)
transportAllocation = rho * (+ 1 / 4)
pathAllocation = rho * (+ 1 / 2)

outerTwoLipschitzFitsExactly :
  (+ 2 / 1) * outerChartRadius ≡ outerAllocation
outerTwoLipschitzFitsExactly = ℚRing.solve []

inverseDexpEnvelope : ℚ → ℚ
inverseDexpEnvelope t =
  (+ 1 / 2) * t + (+ 1 / 6) * t * t

logarithmEnvelopeSlack : ℚ
logarithmEnvelopeSlack =
  logarithmAllocation - inverseDexpEnvelope logarithmChartRadius

logarithmEnvelopePlusSlackExact :
  inverseDexpEnvelope logarithmChartRadius
  + logarithmEnvelopeSlack
  ≡ logarithmAllocation
logarithmEnvelopePlusSlackExact = ℚRing.solve []

logarithmEnvelopeSlackNonnegative :
  0ℚ ≤ logarithmEnvelopeSlack
logarithmEnvelopeSlackNonnegative =
  ℚP.nonNegative⁻¹ logarithmEnvelopeSlack

logarithmEnvelopeFitsAllocation :
  inverseDexpEnvelope logarithmChartRadius
  ≤ logarithmAllocation
logarithmEnvelopeFitsAllocation =
  subst
    (λ upper → inverseDexpEnvelope logarithmChartRadius ≤ upper)
    logarithmEnvelopePlusSlackExact
    (subst
      (λ lower → lower
        ≤ inverseDexpEnvelope logarithmChartRadius
          + logarithmEnvelopeSlack)
      (sym (ℚP.+-identityʳ
        (inverseDexpEnvelope logarithmChartRadius)))
      (ℚP.+-mono-≤ ℚP.≤-refl
        logarithmEnvelopeSlackNonnegative))

minimalPathLength : ℚ
minimalPathLength = + 24 / 1

transportPathBudgetExact :
  minimalPathLength * transportStepRadius ≡ transportAllocation
transportPathBudgetExact = ℚRing.solve []

pathChannelBudgetExact :
  minimalPathLength * pathStepRadius ≡ pathAllocation
pathChannelBudgetExact = ℚRing.solve []

completeCMP109Allocation : ℚ
completeCMP109Allocation =
  outerAllocation
  + (logarithmAllocation
    + (transportAllocation + pathAllocation))

completeCMP109AllocationIsRadius :
  completeCMP109Allocation ≡ rho
completeCMP109AllocationIsRadius = ℚRing.solve []

cmp109OuterRadiusCalibrationLevel : ProofLevel
cmp109OuterRadiusCalibrationLevel = machineChecked

cmp109LogarithmRadiusCalibrationLevel : ProofLevel
cmp109LogarithmRadiusCalibrationLevel = machineChecked

cmp109PathMultiplicityCalibrationLevel : ProofLevel
cmp109PathMultiplicityCalibrationLevel = machineChecked

cmp109PhysicalLeafIdentificationLevel : ProofLevel
cmp109PhysicalLeafIdentificationLevel = conditional
