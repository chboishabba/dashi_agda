module DASHI.Physics.Closure.NSTriadKNLiveOffDiagonalPairFixedResolventMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 Q4+E / ONE LIVE OFF-DIAGONAL PAIR HAS FIXED RESOLVENT WEIGHT
--
-- R560 proves this for a self pair.  Nothing in the fixed-rate argument uses
-- alpha = beta: Fourier geometry, viscosity, and both physical incidences are
-- time-independent.  This owner proves the exact general same-output pair
-- statement needed by the off-diagonal R396 family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; Positive; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNPhysicalTrajectoryRetainedGlobalFluxRound403Exact as R403
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

F : C3.RealField _
F = Rational.rationalRealField

module LivePair
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (T : R240.PhysicalNSDynamics.PhysicalNSGalerkinTrajectory
      Time initialTime integrateTo DerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo DerivativeOf T)
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output)
    (alpha beta : Physical.PhysicalTriadIncidence)
    (alphaOutput : Physical.k alpha ≡ output)
    (betaOutput : Physical.k beta ≡ output) where

  module Dyn = R240.PhysicalNSDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Live = R403.LiveTrajectoryFlux
    Time initialTime integrateTo DerivativeOf

  support : Live.RetainedSupportRealization T
  support = Support.toRetainedSupportRealization T R

  S = Dyn.Base.S (Dyn.forgetDynamics T)
  I = Dyn.Base.I (Dyn.forgetDynamics T)

  physicalSystem : Time → Field30.PhysicalFiniteComplex3GalerkinSystem F
  physicalSystem time = Live.physicalSystemAt T support cutoff time

  rhoAt : Time → Z3.FourierMode → ℚ
  rhoAt time mode = R94.physicalDecayRate (physicalSystem time) mode

  fixedRho : Z3.FourierMode → ℚ
  fixedRho mode =
    C3.multiply F (Dyn.physicalViscosity T) (C3.normSquared I mode)

  rhoAtIsFixed :
    (time : Time) (mode : Z3.FourierMode) →
    rhoAt time mode ≡ fixedRho mode
  rhoAtIsFixed time mode =
    cong
      (λ nu → C3.multiply F nu (C3.normSquared I mode))
      (Dyn.viscosityFixed T cutoff time)

  cellRateAt : Time → Physical.PhysicalTriadIncidence → ℚ
  cellRateAt time tau =
    rhoAt time (Physical.p tau) + rhoAt time (Physical.q tau)

  fixedCellRate : Physical.PhysicalTriadIncidence → ℚ
  fixedCellRate tau =
    fixedRho (Physical.p tau) + fixedRho (Physical.q tau)

  cellRateAtIsFixed :
    (time : Time) (tau : Physical.PhysicalTriadIncidence) →
    cellRateAt time tau ≡ fixedCellRate tau
  cellRateAtIsFixed time tau =
    cong₂ _+_
      (rhoAtIsFixed time (Physical.p tau))
      (rhoAtIsFixed time (Physical.q tau))

  physicalPairAt : Time → R291.DampedCellPair
  physicalPairAt time =
    R389.DoubleMixedPair.physicalDoubleMixedPair
      (physicalSystem time) S alpha beta

  pairRateAt : Time → ℚ
  pairRateAt time = R291.pairRate (physicalPairAt time)

  fixedPairRate : ℚ
  fixedPairRate = fixedCellRate alpha + fixedCellRate beta

  pairRateAtIsFixed : (time : Time) → pairRateAt time ≡ fixedPairRate
  pairRateAtIsFixed time =
    cong₂ _+_
      (cellRateAtIsFixed time alpha)
      (cellRateAtIsFixed time beta)

  pairPositiveAt : (time : Time) → Positive (pairRateAt time)
  pairPositiveAt time =
    let
      viscosityPositive = Live.stateViscosityPositive T support cutoff time
      alphaPositive =
        R400.PhysicalRate.cellRatePositiveFromNonzeroOutput
          (physicalSystem time) S viscosityPositive
          output outputNonzero alpha alphaOutput
      betaPositive =
        R400.PhysicalRate.cellRatePositiveFromNonzeroOutput
          (physicalSystem time) S viscosityPositive
          output outputNonzero beta betaOutput
    in
    R400.PhysicalRate.pairRatePositiveFromCellRates
      (physicalSystem time) S viscosityPositive
      alpha beta alphaPositive betaPositive

  r290At : Time → R290.DampedGramPair
  r290At time =
    R389.DoubleMixedPair.pairRatePositiveBuildsR290
      (physicalSystem time) S alpha beta (pairPositiveAt time)

  fixedWeight : ℚ
  fixedWeight = Reciprocal.safeRationalReciprocal fixedPairRate

  resolventWeightAtIsFixed :
    (time : Time) → R290.resolventWeight (r290At time) ≡ fixedWeight
  resolventWeightAtIsFixed time =
    cong Reciprocal.safeRationalReciprocal (pairRateAtIsFixed time)

  fixedResolventCurve : R416.FixedResolventPairCurve Time
  fixedResolventCurve = record
    { R416.pairAt = r290At
    ; R416.fixedWeight = fixedWeight
    ; R416.resolventWeightFixed = resolventWeightAtIsFixed
    }

roundB7OffDiagonalPairRateTimeInvariant : Bool
roundB7OffDiagonalPairRateTimeInvariant = true

roundB7OffDiagonalResolventWeightTimeInvariant : Bool
roundB7OffDiagonalResolventWeightTimeInvariant = true

roundB7OffDiagonalFixedResolventIntroducesEstimate : Bool
roundB7OffDiagonalFixedResolventIntroducesEstimate = false

roundB7OffDiagonalPairRateTimeInvariantIsTrue :
  roundB7OffDiagonalPairRateTimeInvariant ≡ true
roundB7OffDiagonalPairRateTimeInvariantIsTrue = refl

roundB7OffDiagonalResolventWeightTimeInvariantIsTrue :
  roundB7OffDiagonalResolventWeightTimeInvariant ≡ true
roundB7OffDiagonalResolventWeightTimeInvariantIsTrue = refl
