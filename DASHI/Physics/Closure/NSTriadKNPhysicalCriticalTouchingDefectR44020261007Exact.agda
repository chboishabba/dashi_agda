module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectR44020261007Exact where

------------------------------------------------------------------------
-- POSITIVE B4 / FUSED NONCORE-CORE DEFECT ON THE LITERAL R440 CARRIER
--
-- The fused defect owner leaves one binary-partition residual
--
--   R_NC = n_C W_N + n_N W_C - r_N M_C - r_C M_N,
--
-- where W_X is the input-mass weighted mixed-product fold on subset X and
-- M_X is the ordinary mixed-product fold.
--
-- But inputMass is exactly the canonical input-Laplacian multiplier and the
-- existing R440 weld proves, on ANY incidence list,
--
--   weightedVectorSum inputMass mixedProduct
--     = R440.weightedAmplitudeAggregate.
--
-- Therefore the remaining B4 defect is not an abstract residual-vector
-- problem.  It is exactly one coherent work against a linear combination of
-- four already-owned physical subset folds:
--
--   n_C * R440_N + n_N * R440_C - r_N * M_C - r_C * M_N.
--
-- This file closes only that same-object reduction.  The cutoff-uniform
-- payment of this literal physical combination by the remaining <1/2 M_core
-- allowance plus local ED remains the analytic theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianR440WeldExact as R440Weld
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectNoncoreCore20261007Exact as NoncoreCore
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive

F : C3.RealField _
F = Rational.rationalRealField

module LiveDefectR440
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output
  module N = NoncoreCore.LiveNoncoreCore physicalSystem S output
  module W = R440Weld.PhysicalInputWeight S Live.system

  mixedFold :
    List Physical.PhysicalTriadIncidence → C3.Complex3 F
  mixedFold items = R224.foldVector Live.value items

  weightedFold :
    List Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedFold items =
    Vector.weightedVectorSum Rate.inputMass Live.value items

  r440Fold :
    List Physical.PhysicalTriadIncidence → C3.Complex3 F
  r440Fold items =
    R440.weightedAmplitudeAggregate
      (R440Weld.inputMassWeight Rate.I)
      S Live.system items

  weightedFoldIsR440 :
    (items : List Physical.PhysicalTriadIncidence) →
    weightedFold items ≡ r440Fold items
  weightedFoldIsR440 items =
    W.inputWeightedFoldIsR440 items

  physicalResidual : C3.Complex3 F
  physicalResidual =
    C3.complex3Add
      (R291.realScale
        (Pair.natAsRational (length N.core))
        (r440Fold N.noncore))
      (C3.complex3Add
        (R291.realScale
          (Pair.natAsRational (length N.noncore))
          (r440Fold N.core))
        (C3.complex3Add
          (R291.realScale
            (0ℚ - Pair.rateSum Rate.inputMass N.noncore)
            (mixedFold N.core))
          (R291.realScale
            (0ℚ - Pair.rateSum Rate.inputMass N.core)
            (mixedFold N.noncore))))

  residualIsPhysicalR440NormalForm :
    N.residual ≡ physicalResidual
  residualIsPhysicalR440NormalForm
    rewrite weightedFoldIsR440 N.noncore
          | weightedFoldIsR440 N.core = refl

  defectIsNegativePhysicalR440Work :
    N.R.defect
    ≡ 0ℚ - Work.coherentWork (Live.mixed output) physicalResidual
  defectIsNegativePhysicalR440Work =
    trans
      N.defectIsNegativeVectorWork
      (cong
        (λ residual →
          0ℚ - Work.coherentWork (Live.mixed output) residual)
        residualIsPhysicalR440NormalForm)

------------------------------------------------------------------------
-- Status: all representation content is gone from the B4 defect leaf.
------------------------------------------------------------------------

b4DefectR440SubsetWeldClosed : Bool
b4DefectR440SubsetWeldClosed = true

b4DefectPhysicalResidualNormalFormClosed : Bool
b4DefectPhysicalResidualNormalFormClosed = true

b4DefectSignedPhysicalWorkClosed : Bool
b4DefectSignedPhysicalWorkClosed = true

b4DefectR440PhysicalPaymentClosed : Bool
b4DefectR440PhysicalPaymentClosed = false

b4DefectResidualStillAbstractCarrier : Bool
b4DefectResidualStillAbstractCarrier = false

clayPromotion : Bool
clayPromotion = false

b4DefectR440SubsetWeldClosedIsTrue :
  b4DefectR440SubsetWeldClosed ≡ true
b4DefectR440SubsetWeldClosedIsTrue = refl

b4DefectPhysicalResidualNormalFormClosedIsTrue :
  b4DefectPhysicalResidualNormalFormClosed ≡ true
b4DefectPhysicalResidualNormalFormClosedIsTrue = refl

b4DefectSignedPhysicalWorkClosedIsTrue :
  b4DefectSignedPhysicalWorkClosed ≡ true
b4DefectSignedPhysicalWorkClosedIsTrue = refl

b4DefectR440PhysicalPaymentClosedIsFalse :
  b4DefectR440PhysicalPaymentClosed ≡ false
b4DefectR440PhysicalPaymentClosedIsFalse = refl
