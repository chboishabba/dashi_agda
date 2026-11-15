module DASHI.Physics.Closure.NSVERIDB4PhysicalRateShiftWeldExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFiniteBipartiteCovarianceExact as Bip
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectNoncoreCore20261007Exact as Noncore
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive
import DASHI.Physics.Closure.NSVERIDB4BipartiteRateShiftExact as Shift

F : C3.RealField _
F = Rational.rationalRealField

-- The imported Noncore owner already identifies the literal physical
-- signed defect with minus this bipartite covariance. Here we establish
-- the same-object rate-reference invariance, *not* an absorption bound.
module PhysicalReferenceRate
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module N = Noncore.LiveNoncoreCore physicalSystem S output
  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output

  shiftedPhysicalCovariance : ℚ → ℚ
  shiftedPhysicalCovariance reference =
    Bip.bipartitePairSum
      (Shift.rateShift reference Rate.inputMass)
      (Live.work output)
      N.noncore N.core

  shiftedPhysicalCovarianceEqualsActual :
    (reference : ℚ) →
    shiftedPhysicalCovariance reference ≡ N.covariance
  shiftedPhysicalCovarianceEqualsActual reference =
    Shift.bipartiteRateShiftInvariant
      reference Rate.inputMass (Live.work output)
      N.noncore N.core

  signedDefectEqualsShiftedPhysicalCovariance :
    (reference : ℚ) →
    N.R.defect ≡ 0ℚ - shiftedPhysicalCovariance reference
  signedDefectEqualsShiftedPhysicalCovariance reference =
    trans N.defectIsNegativeNoncoreCore
      (cong (0ℚ -_)
        (sym (shiftedPhysicalCovarianceEqualsActual reference)))

-- No choice of the common reference rate improves the actual defect.
-- The still-open quantitative task is signed, cutoff-uniform control
-- of the physical rate *differences* by actual M_core and local ED.
