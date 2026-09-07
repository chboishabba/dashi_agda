module DASHI.Physics.Closure.NSTriadKNMHDRadiusReciprocalToNormalizedDirectionRound464Exact where

------------------------------------------------------------------------
-- ROUND464 / BIDI X-POLLINATION: MHD RADIUS RECIPROCAL -> NS R455
--
-- The plasma/MHD lane already owns the same-mode reciprocal receipt
--
--   modeNorm(k) * inverseModeNorm(k) = 1.
--
-- R455 had packaged that law together with the independent rational square
-- identification
--
--   modeNorm(k)^2 = normSquared(k).
--
-- This owner removes the duplicated reciprocal obligation.  A consumer now
-- supplies only the square-identification receipt plus the existing MHD
-- ModeRadiusCalibration, and receives the exact R455 calibration expected by
-- the NS normalized-direction/mass pipeline.
--
-- This is a representation compiler only.  It does not claim the square law
-- follows from the weak HelicalModeScalars record or from vector cancellation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact as R455
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedDoubleMixedMassRound456Exact as R456
import DASHI.Physics.Plasma.MHDMagneticVectorPotentialHelicalObserverExact as MHD

F : C3.RealField _
F = Rational.rationalRealField

record RationalModeSquareCalibration
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (mode : Z3.FourierMode) : Set where
  constructor rational-mode-square-calibration
  field
    modeNormSquareMeaning :
      Helical.modeNorm S mode * Helical.modeNorm S mode
      ≡ C3.normSquared I mode

open RationalModeSquareCalibration public

mhdReciprocalAndSquareBuildR455 :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (S : Helical.HelicalModeScalars F)
  (mode : Z3.FourierMode) →
  RationalModeSquareCalibration E I S mode →
  MHD.ModeRadiusCalibration S mode →
  R455.RationalModeRadiusCalibration E I S mode
mhdReciprocalAndSquareBuildR455 E I S mode square reciprocal =
  R455.rational-mode-radius-calibration
    (modeNormSquareMeaning square)
    (MHD.radiusInverse reciprocal)

record PhysicalSquareAndMHDCalibration
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F) : Set where
  constructor physical-square-and-mhd-calibration
  field
    squareCalibration :
      (mode : Z3.FourierMode) → RationalModeSquareCalibration E I S mode
    reciprocalCalibration :
      (mode : Z3.FourierMode) → MHD.ModeRadiusCalibration S mode

open PhysicalSquareAndMHDCalibration public

physicalSquareAndMHDToR456 :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (S : Helical.HelicalModeScalars F) →
  PhysicalSquareAndMHDCalibration E I S →
  R456.PhysicalModeRadiusCalibration E I S
physicalSquareAndMHDToR456 E I S C =
  R456.physical-mode-radius-calibration
    (λ mode →
      mhdReciprocalAndSquareBuildR455 E I S mode
        (squareCalibration C mode)
        (reciprocalCalibration C mode))

round464MHDReciprocalOwnerReused : Bool
round464MHDReciprocalOwnerReused = true

round464DuplicateNSReciprocalFieldRequired : Bool
round464DuplicateNSReciprocalFieldRequired = false

round464OnlySquareIdentificationRemainsNSRepresentationSpecific : Bool
round464OnlySquareIdentificationRemainsNSRepresentationSpecific = true

round464ContainsPostulate : Bool
round464ContainsPostulate = false

round464PackageAClosed : Bool
round464PackageAClosed = false

round464ClayPromotion : Bool
round464ClayPromotion = false

round464DuplicateNSReciprocalFieldRequiredIsFalse :
  round464DuplicateNSReciprocalFieldRequired ≡ false
round464DuplicateNSReciprocalFieldRequiredIsFalse = refl

round464ContainsPostulateIsFalse : round464ContainsPostulate ≡ false
round464ContainsPostulateIsFalse = refl
