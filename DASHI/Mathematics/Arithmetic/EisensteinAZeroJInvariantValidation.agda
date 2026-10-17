module DASHI.Mathematics.Arithmetic.EisensteinAZeroJInvariantValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (0ℚ)

import DASHI.Interop.Round11MachinCrossProverRecognitionExact as Attribution
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EisensteinAZeroJInvariantExact as J

jExpressionOwnerIsDASHINewExtension :
  J.claimOrigin ≡ Attribution.repositoryNewExtension
jExpressionOwnerIsDASHINewExtension = refl

aZeroForcesJExpressionZero :
  ∀ {curve} →
  Elliptic.aCoefficient curve ≡ 0ℚ →
  J.shortWeierstrassJExpression curve ≡ 0ℚ
aZeroForcesJExpressionZero = J.aZeroShortJExpressionIsZero

jExpressionDenominatorCertifiedNonzero :
  (curve : Elliptic.ShortWeierstrassCurve) →
  J.shortJDenominator curve ≡ 0ℚ →
  ⊥
jExpressionDenominatorCertifiedNonzero = J.shortJDenominatorNonzero

noCMTheoryManufactured :
  J.fullCMEndomorphismRingPaid J.canonicalBoundary ≡ false
noCMTheoryManufactured = refl

noHeckeCharacterManufactured :
  J.heckeCharacterPaid J.canonicalBoundary ≡ false
noHeckeCharacterManufactured = refl

noExternalSourceAcquired :
  J.externalScientificSourceAcquiredByThisOwner J.canonicalBoundary ≡ false
noExternalSourceAcquired = refl
