{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNCanonicalInitialCriticalCeilingRound644Exact where

------------------------------------------------------------------------
-- ROUND644 / CANONICAL DYADIC INITIAL CEILING -> LIVE R640 CEILING
--
-- R640 already identifies the live initial critical coordinate with the common
-- R240 initial Fourier datum on the live finite mode list.
--
-- R405 separately identifies that live mode list with the canonical
-- nonzeroCutoffModes N list.  Therefore no infinite-series development is
-- needed in this adapter.  Standard Fourier/Sobolev analysis only has to supply
-- one source receipt:
--
--   sum_{k in nonzeroCutoffModes N}
--     2^(shellIndex k) |u0(k)|^2 <= C(u0)
--
-- uniformly in N.
--
-- R517 already owns the finite-carrier dyadic/Euclidean H^(1/2) multiplier
-- equivalence.  A paper may therefore obtain this source receipt from the
-- standard implication smooth(T^3) -> H^(1/2)(T^3), without formalizing an
-- infinite Fourier series inside this file.
--
-- This module transports that standard-analysis receipt onto the exact live
-- R640.InitialCriticalCeiling consumer.  It introduces no new NS estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNLiteralInitialCriticalRealizationRound640Exact as R640
import DASHI.Physics.Closure.NSTriadKNDyadicCriticalNormEquivalenceBoundaryRound517Exact as R517

F : C3.RealField _
F = Rational.rationalRealField

record CanonicalDyadicInitialCeiling
    (initial : Z3.FourierMode → C3.Complex3 F) : Set where
  field
    cutoffIndependentCeiling : ℚ
    canonicalCutoffBound :
      (cutoff : Nat) →
      R640.weightedInitialDatumMass
        initial
        (Canonical.nonzeroCutoffModes cutoff)
      ≤ cutoffIndependentCeiling

open CanonicalDyadicInitialCeiling public

module InitialCeiling
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus Time DerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Initial = R640.InitialCritical
    Time initialTime integrateTo DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  canonicalReceiptPaysLiveInitialCeiling :
    (D : Live.LiteralRHSTrajectoryData) →
    (R :
      Support.LiteralNonzeroCutoffTrajectory
        (Live.literalPhysicalTrajectory D)) →
    CanonicalDyadicInitialCeiling
      (Live.initialVelocity (Live.support D)) →
    Initial.InitialCriticalCeiling D
  canonicalReceiptPaysLiveInitialCeiling D R ceiling = record
    { Initial.cutoffIndependentInitialCeiling =
        cutoffIndependentCeiling ceiling
    ; Initial.initialDatumCriticalBound = bound
    }
    where
    bound :
      (cutoff : Nat) →
      Initial.initialDatumCritical D cutoff
      ≤ cutoffIndependentCeiling ceiling
    bound cutoff
      rewrite Support.retainedModesExact R cutoff initialTime =
      canonicalCutoffBound ceiling cutoff

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round644FiniteDyadicHOneHalfEquivalenceAlreadyAvailable : Bool
round644FiniteDyadicHOneHalfEquivalenceAlreadyAvailable =
  R517.round517UniformDyadicHOneHalfEquivalenceClosed

round644CanonicalDyadicSourceReceiptTyped : Bool
round644CanonicalDyadicSourceReceiptTyped = true

round644CanonicalDyadicReceiptToLiveR640CeilingClosed : Bool
round644CanonicalDyadicReceiptToLiveR640CeilingClosed = true

round644InfiniteFourierSeriesFormalizationRequiredHere : Bool
round644InfiniteFourierSeriesFormalizationRequiredHere = false

round644StandardSmoothToHOneHalfSourceStillExternal : Bool
round644StandardSmoothToHOneHalfSourceStillExternal = true

round644IntroducesNewNSEstimate : Bool
round644IntroducesNewNSEstimate = false

round644ClayPromotion : Bool
round644ClayPromotion = false

round644FiniteDyadicHOneHalfEquivalenceAlreadyAvailableIsTrue :
  round644FiniteDyadicHOneHalfEquivalenceAlreadyAvailable ≡ true
round644FiniteDyadicHOneHalfEquivalenceAlreadyAvailableIsTrue =
  R517.round517UniformDyadicHOneHalfEquivalenceClosedIsTrue

round644CanonicalDyadicSourceReceiptTypedIsTrue :
  round644CanonicalDyadicSourceReceiptTyped ≡ true
round644CanonicalDyadicSourceReceiptTypedIsTrue = refl

round644CanonicalDyadicReceiptToLiveR640CeilingClosedIsTrue :
  round644CanonicalDyadicReceiptToLiveR640CeilingClosed ≡ true
round644CanonicalDyadicReceiptToLiveR640CeilingClosedIsTrue = refl

round644InfiniteFourierSeriesFormalizationRequiredHereIsFalse :
  round644InfiniteFourierSeriesFormalizationRequiredHere ≡ false
round644InfiniteFourierSeriesFormalizationRequiredHereIsFalse = refl

round644StandardSmoothToHOneHalfSourceStillExternalIsTrue :
  round644StandardSmoothToHOneHalfSourceStillExternal ≡ true
round644StandardSmoothToHOneHalfSourceStillExternalIsTrue = refl

round644IntroducesNewNSEstimateIsFalse :
  round644IntroducesNewNSEstimate ≡ false
round644IntroducesNewNSEstimateIsFalse = refl

round644ClayPromotionIsFalse :
  round644ClayPromotion ≡ false
round644ClayPromotionIsFalse = refl
