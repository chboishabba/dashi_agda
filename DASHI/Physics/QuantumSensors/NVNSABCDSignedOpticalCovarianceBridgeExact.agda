module DASHI.Physics.QuantumSensors.NVNSABCDSignedOpticalCovarianceBridgeExact where

-- Reuse the actual NS A/B/C/D division-free signed covariance theorem
-- as algebra on finite optical alternative labels. No identification of
-- photon amplitudes with Navier-Stokes velocity/viscous dissipation.
-- Donor: NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact.
-- The finite rate/real-work data need a physical optical producer.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.List.Base using (List; length)
import DASHI.Physics.Closure.NSIntegerFourierLattice as NSMode
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as NS

record OpticalFourierAlternative : Set where
  constructor optical-alternative
  field
    mode : NSMode.FourierMode
    dampingRate : ℚ
    signedInterferenceWork : ℚ
open OpticalFourierAlternative public

opticalDampingSum : List OpticalFourierAlternative → ℚ
opticalDampingSum = NS.rateSum dampingRate

opticalWorkSum : List OpticalFourierAlternative → ℚ
opticalWorkSum = NS.workSum signedInterferenceWork

opticalRateWeightedWork : List OpticalFourierAlternative → ℚ
opticalRateWeightedWork =
  NS.weightedWorkSum dampingRate signedInterferenceWork

opticalSignedPairDifference : List OpticalFourierAlternative → ℚ
opticalSignedPairDifference =
  NS.pairDifferenceWorkSum dampingRate signedInterferenceWork

-- The same exact *signed* cancellation/centering identity as in NS;
-- taking absolute values termwise before centering can lose cancellations.
opticalDivisionFreeSignedCentering :
  (paths : List OpticalFourierAlternative) →
  NS.natAsRational (length paths) * (0ℚ - opticalRateWeightedWork paths)
    + opticalDampingSum paths * opticalWorkSum paths
  ≡ 0ℚ - opticalSignedPairDifference paths
opticalDivisionFreeSignedCentering =
  NS.divisionFreePairDifferenceCentering
    dampingRate signedInterferenceWork

-- Only a finite Fourier-mode index is imported from the NS lattice;
-- physical NS shell bounds/Clay conclusions are NOT transported.
record OpticalModeMatch : Set where
  constructor optical-mode-match
  field
    inputLeft inputRight output : NSMode.FourierMode
    frequencyClosure : NSMode.addMode inputLeft inputRight ≡ output
open OpticalModeMatch public
