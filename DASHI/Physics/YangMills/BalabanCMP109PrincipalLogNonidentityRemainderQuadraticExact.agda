module DASHI.Physics.YangMills.BalabanCMP109PrincipalLogNonidentityRemainderQuadraticExact where

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
-- The merged Round-47 module fixes the same-object coordinate/trivialization
-- seam but intentionally leaves the local analytic remainder conditional.
-- Here we prove the quantitative estimate used to close that leaf once the
-- source mean-value identity and the already-owned local Jacobian Lipschitz
-- estimate are instantiated:
--
--   ||J_{G,xi}-J_G|| <= L ||xi||,
--   ||r_G(xi)||      <= ||J_{G,xi}-J_G|| ||xi||
--
-- imply
--
--   ||r_G(xi)|| <= L ||xi||^2,
--
-- and therefore, whenever L||xi|| <= epsilon,
--
--   ||r_G(xi)|| <= epsilon ||xi||.
--
-- This is the exact epsilon-form needed by the Federbush equation-(0.11)
-- reopening.  No second derivative object or norm conversion is introduced.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

record PrincipalLogMeanValueRemainderData
    (inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude : ℚ)
    : Set where
  field
    inputNonnegative : 0ℚ ≤ inputMagnitude
    jacobianVariationNonnegative : 0ℚ ≤ jacobianVariation
    remainderNonnegative : 0ℚ ≤ remainderMagnitude
    jacobianLipschitz :
      jacobianVariation ≤ lipschitzConstant * inputMagnitude
    meanValueRemainderBound :
      remainderMagnitude ≤ jacobianVariation * inputMagnitude

open PrincipalLogMeanValueRemainderData public

principalLogNonidentityRemainderQuadratic :
  ∀ inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude →
  PrincipalLogMeanValueRemainderData
    inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude →
  remainderMagnitude
    ≤ (lipschitzConstant * inputMagnitude) * inputMagnitude
principalLogNonidentityRemainderQuadratic
    inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude data =
  ℚP.≤-trans
    (meanValueRemainderBound data)
    (ℚP.*-monoʳ-≤-nonNeg inputMagnitude (jacobianLipschitz data))

principalLogNonidentityRemainderLittleOEpsilon :
  ∀ inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude epsilon →
  PrincipalLogMeanValueRemainderData
    inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude →
  lipschitzConstant * inputMagnitude ≤ epsilon →
  remainderMagnitude ≤ epsilon * inputMagnitude
principalLogNonidentityRemainderLittleOEpsilon
    inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude epsilon
    data small =
  ℚP.≤-trans
    (principalLogNonidentityRemainderQuadratic
      inputMagnitude lipschitzConstant jacobianVariation remainderMagnitude data)
    (ℚP.*-monoʳ-≤-nonNeg inputMagnitude small)

cmp109PrincipalLogNonidentityQuadraticRemainderLevel : ProofLevel
cmp109PrincipalLogNonidentityQuadraticRemainderLevel = machineChecked

cmp109PrincipalLogNonidentityEpsilonLittleOLevel : ProofLevel
cmp109PrincipalLogNonidentityEpsilonLittleOLevel = machineChecked
