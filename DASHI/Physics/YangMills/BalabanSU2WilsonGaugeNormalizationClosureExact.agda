module DASHI.Physics.YangMills.BalabanSU2WilsonGaugeNormalizationClosureExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 1ℚ; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact using
  (positivePlaquetteMultiplicity)
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate using
  (configuredPathCoercivityConstant)
open import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate using
  (oneSixteenth)

------------------------------------------------------------------------
-- Configured convention fixed by the exact quaternion jet and six-plane fold.
------------------------------------------------------------------------

cTrace cWilson cOrientation cGauge : ℚ
cTrace = 1ℚ
cWilson = 1ℚ
cOrientation = positivePlaquetteMultiplicity
cGauge = 1ℚ

configuredWilsonGaugeNormalization : ℚ
configuredWilsonGaugeNormalization =
  cTrace * (cWilson * (cOrientation * cGauge))

configuredWilsonGaugeNormalizationExact :
  configuredWilsonGaugeNormalization ≡ 1ℚ
configuredWilsonGaugeNormalizationExact = ℚRing.solve-∀

configuredReferenceConstantIsPurePoincare :
  configuredPathCoercivityConstant ≡ oneSixteenth
configuredReferenceConstantIsPurePoincare = ℚRing.solve-∀

su2WilsonGaugeNormalizationClosureLevel : ProofLevel
su2WilsonGaugeNormalizationClosureLevel = machineChecked
