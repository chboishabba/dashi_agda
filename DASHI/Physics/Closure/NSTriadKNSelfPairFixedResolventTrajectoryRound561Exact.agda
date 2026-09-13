module DASHI.Physics.Closure.NSTriadKNSelfPairFixedResolventTrajectoryRound561Exact where

------------------------------------------------------------------------
-- ROUND561 / R240 FIXED VISCOSITY -> FIXED SELF-PAIR R290 RESOLVENT WEIGHT
--
-- On the Round228 trajectory, E/I/S are static.  Round240 additionally proves
-- one viscosity is shared by every cutoff and time.  Therefore for a fixed
-- physical incidence tau the double-mixed cell rate is time-independent, as is
-- the self-pair rate and hence R384's constructive rational reciprocal.
--
-- This owner packages the literal time-indexed R389 self pair directly as the
-- R416.FixedResolventPairCurve and R418.SameR291R290PairCurve consumed by the
-- existing derivative compilers.  No heat/Laplace representation and no new
-- positivity premise are introduced: R405 supplies positive physical viscosity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; Positive)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR291R290SamePairDerivativeRound418Exact as R418
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

F : C3.RealField _
F = Rational.rationalRealField

module FixedSelfPair
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Live = R408.LiteralDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf

  trajectory : Live.LiteralRHSTrajectoryData → Dyn.PhysicalNSGalerkinTrajectory
  trajectory = Live.literalPhysicalTrajectory

  commonNu : Live.LiteralRHSTrajectoryData → ℚ
  commonNu D = Dyn.physicalViscosity (trajectory D)

  inverseSquare :
    (D : Live.LiteralRHSTrajectoryData) →
    C3.ModeInverseSquare F (Live.Base.E (Live.stateTrajectory (Live.support D)))
  inverseSquare D = Live.Base.I (Live.stateTrajectory (Live.support D))

  physicalSystemAt :
    Live.LiteralRHSTrajectoryData → Nat → Time →
    Field30.PhysicalFiniteComplex3GalerkinSystem F
  physicalSystemAt D cutoff time =
    Live.physicalSystemAt (Live.support D) cutoff time

  currentViscosityFixed561 :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) (time : Time) →
    Field30.viscosity (physicalSystemAt D cutoff time) ≡ commonNu D
  currentViscosityFixed561 D cutoff time =
    Dyn.viscosityFixed (trajectory D) cutoff time

  currentViscosityPositive561 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (trajectory D)) →
    (cutoff : Nat) (time : Time) →
    Positive (Field30.viscosity (physicalSystemAt D cutoff time))
  currentViscosityPositive561 D R cutoff time =
    subst Positive
      (sym (currentViscosityFixed561 D cutoff time))
      (Support.physicalViscosityPositive R)

  fixedDecayRate561 :
    (D : Live.LiteralRHSTrajectoryData) →
    Z3.FourierMode → ℚ
  fixedDecayRate561 D mode =
    C3.multiply F (commonNu D)
      (C3.normSquared (inverseSquare D) mode)

  physicalDecayRateFixed561 :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) (time : Time) →
    (mode : Z3.FourierMode) →
    R94.physicalDecayRate (physicalSystemAt D cutoff time) mode
    ≡ fixedDecayRate561 D mode
  physicalDecayRateFixed561 D cutoff time mode =
    cong
      (λ selected →
        C3.multiply F selected
          (C3.normSquared (inverseSquare D) mode))
      (currentViscosityFixed561 D cutoff time)

  fixedCellRate561 :
    (D : Live.LiteralRHSTrajectoryData) →
    Physical.PhysicalTriadIncidence → ℚ
  fixedCellRate561 D tau =
    fixedDecayRate561 D (Physical.p tau)
      + fixedDecayRate561 D (Physical.q tau)

  cellRateFixed561 :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) (time : Time) →
    (tau : Physical.PhysicalTriadIncidence) →
    let module Pair = R389.DoubleMixedPair (physicalSystemAt D cutoff time) S
    in Pair.D.Pair.cellRate tau ≡ fixedCellRate561 D tau
  cellRateFixed561 D S cutoff time tau =
    cong₂ _+_
      (physicalDecayRateFixed561 D cutoff time (Physical.p tau))
      (physicalDecayRateFixed561 D cutoff time (Physical.q tau))

  fixedSelfPairRate561 :
    (D : Live.LiteralRHSTrajectoryData) →
    Physical.PhysicalTriadIncidence → ℚ
  fixedSelfPairRate561 D tau =
    fixedCellRate561 D tau + fixedCellRate561 D tau

  selfPairRateFixed561 :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) (time : Time) →
    (tau : Physical.PhysicalTriadIncidence) →
    let module Pair = R389.DoubleMixedPair (physicalSystemAt D cutoff time) S
    in
    R291.pairRate (Pair.physicalDoubleMixedPair tau tau)
    ≡ fixedSelfPairRate561 D tau
  selfPairRateFixed561 D S cutoff time tau =
    cong₂ _+_
      (cellRateFixed561 D S cutoff time tau)
      (cellRateFixed561 D S cutoff time tau)

  selfPairPositiveAt561 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) (time : Time) →
    (output : Z3.FourierMode) →
    Z3.NonZeroMode output →
    (tau : Physical.PhysicalTriadIncidence) →
    Physical.k tau ≡ output →
    let module Pair = R389.DoubleMixedPair (physicalSystemAt D cutoff time) S
    in Positive (R291.pairRate (Pair.physicalDoubleMixedPair tau tau))
  selfPairPositiveAt561 D R S cutoff time output outputNonzero tau outputExact =
    let
      PS = physicalSystemAt D cutoff time
      module Pair = R389.DoubleMixedPair PS S
      module Rate = R400.PhysicalRate
        PS S (currentViscosityPositive561 D R cutoff time)
      cellPositive =
        Rate.cellRatePositiveFromNonzeroOutput
          output outputNonzero tau outputExact
    in
    Rate.pairRatePositiveFromCellRates
      tau tau cellPositive cellPositive

  r291SelfPairAt561 :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (tau : Physical.PhysicalTriadIncidence) →
    Time → R291.DampedCellPair
  r291SelfPairAt561 D S cutoff tau time =
    let module Pair = R389.DoubleMixedPair (physicalSystemAt D cutoff time) S
    in Pair.physicalDoubleMixedPair tau tau

  r290SelfPairAt561 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (tau : Physical.PhysicalTriadIncidence) →
    Physical.k tau ≡ output →
    Time → R290.DampedGramPair
  r290SelfPairAt561 D R S cutoff output outputNonzero tau outputExact time =
    let
      module Pair = R389.DoubleMixedPair (physicalSystemAt D cutoff time) S
    in
    Pair.pairRatePositiveBuildsR290 tau tau
      (selfPairPositiveAt561
        D R S cutoff time output outputNonzero tau outputExact)

  fixedWeight561 :
    (D : Live.LiteralRHSTrajectoryData) →
    Physical.PhysicalTriadIncidence → ℚ
  fixedWeight561 D tau =
    Reciprocal.safeRationalReciprocal (fixedSelfPairRate561 D tau)

  resolventWeightFixed561 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (tau : Physical.PhysicalTriadIncidence) →
    (outputExact : Physical.k tau ≡ output) →
    (time : Time) →
    R290.resolventWeight
      (r290SelfPairAt561
        D R S cutoff output outputNonzero tau outputExact time)
    ≡ fixedWeight561 D tau
  resolventWeightFixed561 D R S cutoff output outputNonzero tau outputExact time =
    cong Reciprocal.safeRationalReciprocal
      (selfPairRateFixed561 D S cutoff time tau)

  r291Curve561 :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (tau : Physical.PhysicalTriadIncidence) →
    R417.DampedCellPairCurve Time
  r291Curve561 D S cutoff tau = record
    { R417.pairAt = r291SelfPairAt561 D S cutoff tau }

  r290Curve561 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (tau : Physical.PhysicalTriadIncidence) →
    (outputExact : Physical.k tau ≡ output) →
    R416.FixedResolventPairCurve Time
  r290Curve561 D R S cutoff output outputNonzero tau outputExact = record
    { R416.pairAt =
        r290SelfPairAt561
          D R S cutoff output outputNonzero tau outputExact
    ; R416.fixedWeight = fixedWeight561 D tau
    ; R416.resolventWeightFixed =
        resolventWeightFixed561
          D R S cutoff output outputNonzero tau outputExact
    }

  sameR291R290SelfPairCurve561 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (tau : Physical.PhysicalTriadIncidence) →
    (outputExact : Physical.k tau ≡ output) →
    R418.SameR291R290PairCurve Time
  sameR291R290SelfPairCurve561
      D R S cutoff output outputNonzero tau outputExact = record
    { R418.r291Curve = r291Curve561 D S cutoff tau
    ; R418.r290Curve =
        r290Curve561 D R S cutoff output outputNonzero tau outputExact
    ; R418.sameGram = λ time → refl
    ; R418.sameGramTangent = λ time → refl
    }

round561R240FixedViscosityPaysCellRateConstancy : Bool
round561R240FixedViscosityPaysCellRateConstancy = true

round561R405PositiveViscosityReused : Bool
round561R405PositiveViscosityReused = true

round561SelfPairRateFixed : Bool
round561SelfPairRateFixed = true

round561SelfPairResolventWeightFixed : Bool
round561SelfPairResolventWeightFixed = true

round561R418SamePairCurveConstructed : Bool
round561R418SamePairCurveConstructed = true

round561HeatRepresentationUsed : Bool
round561HeatRepresentationUsed = false

round561FiniteSelfPairFamilyStillOpen : Bool
round561FiniteSelfPairFamilyStillOpen = true

round561ClayPromotion : Bool
round561ClayPromotion = false

round561SelfPairResolventWeightFixedIsTrue :
  round561SelfPairResolventWeightFixed ≡ true
round561SelfPairResolventWeightFixedIsTrue = refl

round561R418SamePairCurveConstructedIsTrue :
  round561R418SamePairCurveConstructed ≡ true
round561R418SamePairCurveConstructedIsTrue = refl

round561HeatRepresentationUsedIsFalse :
  round561HeatRepresentationUsed ≡ false
round561HeatRepresentationUsedIsFalse = refl

round561ClayPromotionIsFalse : round561ClayPromotion ≡ false
round561ClayPromotionIsFalse = refl
