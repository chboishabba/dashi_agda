module DASHI.Physics.Closure.NSTriadKNLiveSelfPairFixedResolventRound560Exact where

------------------------------------------------------------------------
-- ROUND560 / LIVE SELF-PAIR RATE AND RESOLVENT WEIGHT ARE TIME-FIXED
--
-- R559 reduces actual self-flux differentiation to a finite family of R418
-- same-pair curves. R416 requires each resolvent weight to be fixed in time.
-- On the live R240 trajectory this follows from existing same-object data:
--
--   * the Fourier embedding/inverse-square data are trajectory fields;
--   * R240 owns one physical viscosity and every state viscosity equals it;
--   * the physical triad indices are fixed.
--
-- Thus rho(mode)=nu |mode|^2, the self-pair rate 2(rho_p+rho_q), and its
-- constructive reciprocal are time-independent. No analytic estimate appears.
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

module LiveSelfPair
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
    (alpha : Physical.PhysicalTriadIncidence)
    (outputExact : Physical.k alpha ≡ output) where

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

  cellRateAt : Time → ℚ
  cellRateAt time = rhoAt time (Physical.p alpha) + rhoAt time (Physical.q alpha)

  fixedCellRate : ℚ
  fixedCellRate = fixedRho (Physical.p alpha) + fixedRho (Physical.q alpha)

  cellRateAtIsFixed : (time : Time) → cellRateAt time ≡ fixedCellRate
  cellRateAtIsFixed time =
    cong₂ _+_
      (rhoAtIsFixed time (Physical.p alpha))
      (rhoAtIsFixed time (Physical.q alpha))

  physicalPairAt : Time → R291.DampedCellPair
  physicalPairAt time =
    R389.DoubleMixedPair.physicalDoubleMixedPair
      (physicalSystem time) S alpha alpha

  pairRateAt : Time → ℚ
  pairRateAt time = R291.pairRate (physicalPairAt time)

  fixedPairRate : ℚ
  fixedPairRate = fixedCellRate + fixedCellRate

  pairRateAtIsFixed : (time : Time) → pairRateAt time ≡ fixedPairRate
  pairRateAtIsFixed time =
    cong₂ _+_ (cellRateAtIsFixed time) (cellRateAtIsFixed time)

  selfPairPositiveAt : (time : Time) → Positive (pairRateAt time)
  selfPairPositiveAt time =
    let
      viscosityPositive = Live.stateViscosityPositive T support cutoff time
      cellPositive =
        R400.PhysicalRate.cellRatePositiveFromNonzeroOutput
          (physicalSystem time) S viscosityPositive
          output outputNonzero alpha outputExact
    in
    R400.PhysicalRate.pairRatePositiveFromCellRates
      (physicalSystem time) S viscosityPositive
      alpha alpha cellPositive cellPositive

  selfR290At : Time → R290.DampedGramPair
  selfR290At time =
    R389.DoubleMixedPair.pairRatePositiveBuildsR290
      (physicalSystem time) S alpha alpha (selfPairPositiveAt time)

  fixedWeight : ℚ
  fixedWeight = Reciprocal.safeRationalReciprocal fixedPairRate

  resolventWeightAtIsFixed :
    (time : Time) → R290.resolventWeight (selfR290At time) ≡ fixedWeight
  resolventWeightAtIsFixed time =
    cong Reciprocal.safeRationalReciprocal (pairRateAtIsFixed time)

  fixedResolventCurve : R416.FixedResolventPairCurve Time
  fixedResolventCurve = record
    { R416.pairAt = selfR290At
    ; R416.fixedWeight = fixedWeight
    ; R416.resolventWeightFixed = resolventWeightAtIsFixed
    }

round560TrajectoryFourierGeometryFixed : Bool
round560TrajectoryFourierGeometryFixed = true

round560TrajectoryViscosityFixesCellRate : Bool
round560TrajectoryViscosityFixesCellRate = true

round560SelfPairRateTimeInvariant : Bool
round560SelfPairRateTimeInvariant = true

round560SelfPairResolventWeightTimeInvariant : Bool
round560SelfPairResolventWeightTimeInvariant = true

round560IntroducesNewAnalyticEstimate : Bool
round560IntroducesNewAnalyticEstimate = false

round560ClayPromotion : Bool
round560ClayPromotion = false

round560SelfPairRateTimeInvariantIsTrue :
  round560SelfPairRateTimeInvariant ≡ true
round560SelfPairRateTimeInvariantIsTrue = refl

round560SelfPairResolventWeightTimeInvariantIsTrue :
  round560SelfPairResolventWeightTimeInvariant ≡ true
round560SelfPairResolventWeightTimeInvariantIsTrue = refl

round560ClayPromotionIsFalse : round560ClayPromotion ≡ false
round560ClayPromotionIsFalse = refl
