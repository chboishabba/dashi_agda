module DASHI.Physics.Closure.NSTriadKNLiveR406DiagonalReducedNormalFormRound556Exact where

------------------------------------------------------------------------
-- ROUND556 / LIVE R406 SLICE SPECIALIZATION OF R555
--
-- R406 already owns the literal physical system at every (N,t), its canonical
-- nonzero output list, the exact R398 positivity witness, and the physical
-- helicity receipt.  R404 proves every member of that output list is nonzero.
-- Therefore R555 specializes directly to the literal live R406 remainder.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNGlobalDiagonalReducedNormalFormRound555Exact as R555

F : C3.RealField _
F = Rational.rationalRealField

module LiveReduced
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo DerivativeOf

  module At
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat)
      (time : Time) where

    module Slice = Flux.At T R cutoff time

    S = Dyn.Base.S (Dyn.forgetDynamics T)
    L = Dyn.Base.L (Dyn.forgetDynamics T)
    H = Dyn.Base.H (Dyn.forgetDynamics T)

    module GR = R555.GlobalReduced
      Slice.PS S L H Slice.P
      (Flux.Live.stateViscosityPositive T Slice.support cutoff time)

    buildOutputsNonzero :
      (items : List Z3.FourierMode) →
      ((mode : Z3.FourierMode) → mode Cube.∈ items → Z3.NonZeroMode mode) →
      GR.OutputsNonzero items
    buildOutputsNonzero [] allNonzero = GR.nonzeroNil
    buildOutputsNonzero (mode ∷ rest) allNonzero =
      GR.nonzeroCons
        (allNonzero mode (Cube.here refl))
        (buildOutputsNonzero rest
          (λ selected member → allNonzero selected (Cube.there member)))

    canonicalOutputsNonzero : GR.OutputsNonzero Slice.outputs
    canonicalOutputsNonzero =
      buildOutputsNonzero Slice.outputs
        (λ mode member → R404.nonzeroCutoffMemberNonzero member)

    liveFactoredFull : ℚ
    liveFactoredFull =
      GR.globalFactoredFull cutoff Slice.outputs canonicalOutputsNonzero

    liveSelfGram : ℚ
    liveSelfGram =
      GR.globalSelfGram cutoff Slice.outputs canonicalOutputsNonzero

    liveSelfFluxTangent : ℚ
    liveSelfFluxTangent =
      GR.globalSelfFluxTangent cutoff Slice.outputs canonicalOutputsNonzero

    twoLiteralR406RemainderIsReducedNormalForm :
      R539.two * Slice.weightedRemainder
      ≡ (liveFactoredFull - liveSelfGram) - liveSelfFluxTangent
    twoLiteralR406RemainderIsReducedNormalForm =
      GR.globalDiagonalReducedNormalForm
        cutoff Slice.outputs Slice.canonicalOutputPositivity canonicalOutputsNonzero

round556LiveR406SliceWeldClosed : Bool
round556LiveR406SliceWeldClosed = true

round556CanonicalOutputNonzeroReceiptReused : Bool
round556CanonicalOutputNonzeroReceiptReused = true

round556IntroducesAnyAnalyticEstimate : Bool
round556IntroducesAnyAnalyticEstimate = false

round556TemporalIntegrationClosed : Bool
round556TemporalIntegrationClosed = false

round556FactoredFullSpacetimeBoundClosed : Bool
round556FactoredFullSpacetimeBoundClosed = false

round556ClayPromotion : Bool
round556ClayPromotion = false

round556LiveR406SliceWeldClosedIsTrue :
  round556LiveR406SliceWeldClosed ≡ true
round556LiveR406SliceWeldClosedIsTrue = refl

round556ClayPromotionIsFalse : round556ClayPromotion ≡ false
round556ClayPromotionIsFalse = refl
