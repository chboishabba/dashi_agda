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

------------------------------------------------------------------------
-- 2026-10-24 NEGATIVE CONTROL / DO NOT PROMOTE FULL-FIBRE B4 PAYMENT
--
-- For the fixed smooth unforced shear u0=2(cos x+cos y)e_z, k=(1,1,0),
-- two active Core mixed-helicity cells have rate 2, M=(-i/2,-i/2,0).
-- Every OTHER incidence is zero in amplitude, but the full enumeration
-- still contributes zero-cell counts and input-rate sums to noncore
-- centering. Exact physical negative-control arithmetic gives
--
--    defect_N = sum_Noncore (|p|^2+|q|^2-2) -> +infinity,
--
-- while the literal Core-Core Young companion freezes at 1345859672
-- for N>=9. In particular, defect_40=1671172320.
--
-- Hence the proposed defect <= theta*M_core + c*localED CANNOT be cutoff
-- uniform IF localED is a genuine bounded physical quantity on this
-- fixed smooth state. The analytic interface currently does not source
-- localED, so this is a conditional NO-GO for the intended physical
-- payment, NOT a kernel proof of failure of an independently specified
-- ED predicate. Do not change the closed-status flag to true.
--
-- THE REAL ED PROVENANCE IS ALREADY FIXED (NOT AN OPAQUE CUT):
-- R219.physicalModalED has E_m=||u_m||² and D_m=|m|²||u_m||².
-- R109.pairKernel(p,q)=D_p E_q + E_p D_q.
-- R469.selectedTriadValue routes that kernel through the selected
-- ordered output fibre, and PhysicalCriticalRegionUniformFamilyProducer
-- defines localED(k) as its fold. A selected Boolean may ONLY remove
-- nonnegative terms. For the same fixed seed, sum E=sum D=4,
-- so the GLOBAL selected pair ED<=2*4*4=32 and this output's
-- selected localED(k)<=4 (only ordered (e_x,e_y),(e_y,e_x) can be
-- nonzero, each ED kernel =2). Both bounds are INDEPENDENT of N.
--
-- Thus the literal B4 physical payment against this original ED
-- source is mathematically impossible with cutoff-independent
-- theta_D<1/2 and c_D: defect_N diverges, M_core is fixed,
-- localED<=4. A generic source-attachment record still permits an
-- arbitrary nonspecific localED and is NOT the original physical ED.
-- This is a no-go for THIS auxiliary B4 full-fibre estimate, not
-- a no-go for Navier-Stokes or for a redesigned R440 estimator.
--
-- Source/receipt: scripts/ns_b4_literal_padding_adversary.py
-- Canonical fix: derive a zero-padding-invariant bound from the literal
-- modal R440 weighted amplitude, preserving NS source identification;
-- zero rows must not create spectral damping work.
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
