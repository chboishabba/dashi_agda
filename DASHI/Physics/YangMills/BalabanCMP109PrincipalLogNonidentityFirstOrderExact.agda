module DASHI.Physics.YangMills.BalabanCMP109PrincipalLogNonidentityFirstOrderExact where

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
-- "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction",
-- second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Quantitative remainder closure for the nonidentity principal logarithm.
-- The source calculus gives a line/mean-value remainder controlled by the
-- variation of the left/right-trivialized logarithm Jacobian.  The existing
-- CMP109 SU(2) modules prove a local Lipschitz bound for that Jacobian.  This
-- module performs the missing estimate, without changing trivialization:
--
--   ||J_{G,xi}-J_G|| <= L ||xi||
--   ||r_G(xi)||      <= ||J_{G,xi}-J_G|| ||xi||
--
-- imply
--
--   ||r_G(xi)|| <= L ||xi||^2.
--
-- Hence whenever L ||xi|| <= epsilon,
--
--   ||r_G(xi)|| <= epsilon ||xi||,
--
-- which is the exact epsilon-form consumed by the Federbush reopening.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

record NonidentityPrincipalLogRemainderData
    (inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude : ℚ)
    : Set where
  field
    inputNonnegative : 0ℚ ≤ inputMagnitude
    jacobianVariationNonnegative : 0ℚ ≤ jacobianVariation
    remainderNonnegative : 0ℚ ≤ remainderMagnitude
    jacobianLipschitz :
      jacobianVariation ≤ lipschitzConstant * inputMagnitude
    sourceMeanValueRemainder :
      remainderMagnitude ≤ jacobianVariation * inputMagnitude

open NonidentityPrincipalLogRemainderData public

principalLogNonidentityQuadraticRemainder :
  ∀ inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude →
  NonidentityPrincipalLogRemainderData
    inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude →
  remainderMagnitude
    ≤ (lipschitzConstant * inputMagnitude) * inputMagnitude
principalLogNonidentityQuadraticRemainder
    inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude data =
  ℚP.≤-trans
    (sourceMeanValueRemainder data)
    (ℚP.*-monoʳ-≤-nonNeg inputMagnitude
      (jacobianLipschitz data))

principalLogNonidentityLittleOEpsilon :
  ∀ inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude epsilon →
  NonidentityPrincipalLogRemainderData
    inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude →
  lipschitzConstant * inputMagnitude ≤ epsilon →
  remainderMagnitude ≤ epsilon * inputMagnitude
principalLogNonidentityLittleOEpsilon
    inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude epsilon
    data small =
  ℚP.≤-trans
    (principalLogNonidentityQuadraticRemainder
      inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude data)
    (ℚP.*-monoʳ-≤-nonNeg inputMagnitude small)

cmp109PrincipalLogNonidentityQuadraticRemainderLevel : ProofLevel
cmp109PrincipalLogNonidentityQuadraticRemainderLevel = machineChecked

cmp109PrincipalLogNonidentityLittleOEpsilonLevel : ProofLevel
cmp109PrincipalLogNonidentityLittleOEpsilonLevel = machineChecked
