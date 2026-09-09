module DASHI.Physics.Closure.NSTriadKNLiteralSelfPairDerivativeItemRound562Exact where

------------------------------------------------------------------------
-- ROUND562 / ONE LITERAL R240 SELF PAIR -> R422 PAIR-DERIVATIVE ITEM
--
-- R560 proves the actual derivative of the live double-mixed cell is the stored
-- R388 tangent.  R561 packages the same stored self pair as an R418
-- SameR291R290PairCurve with fixed constructive resolvent weight.
--
-- For a self pair the two R417 cell-derivative premises are therefore the same
-- literal theorem.  This owner packages one physical incidence directly as the
-- PairCurveDerivativeData consumed by R559/R412 finite summation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR291R290SamePairDerivativeRound418Exact as R418
import DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact as R422
import DASHI.Physics.Closure.NSTriadKNLiteralDoubleMixedTangentTrajectoryWeldRound560Exact as R560
import DASHI.Physics.Closure.NSTriadKNSelfPairFixedResolventTrajectoryRound561Exact as R561

F : C3.RealField _
F = Rational.rationalRealField

module LiteralSelfPairItem
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (projectedCross : R426.ProjectedCrossDerivativeCalculus Time DerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time DerivativeOf) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Tangent = R560.LiteralDoubleMixedTrajectory
    Time initialTime integrateTo DerivativeOf projectedCross vectorAlgebra
  module Fixed = R561.FixedSelfPair
    Time initialTime integrateTo DerivativeOf

  pairCurve562 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (tau : Physical.PhysicalTriadIncidence) →
    (outputExact : Physical.k tau ≡ output) →
    R418.SameR291R290PairCurve Time
  pairCurve562 = Fixed.sameR291R290SelfPairCurve561

  cellDerivative562 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (tau : Physical.PhysicalTriadIncidence) →
    (outputExact : Physical.k tau ≡ output) →
    let P = pairCurve562 D R S cutoff output outputNonzero tau outputExact
    in
    DerivativeOf
      (R417.cellACurve (R418.r291Curve P))
      (R417.tangentACurve (R418.r291Curve P))
  cellDerivative562 D R S cutoff output outputNonzero tau outputExact =
    Tangent.actualDoubleMixedDerivativeIsStoredR388Tangent560
      D S cutoff tau

  literalSelfPairDerivativeItem562 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (tau : Physical.PhysicalTriadIncidence) →
    (outputExact : Physical.k tau ≡ output) →
    R422.PairCurveDerivativeData Time DerivativeOf
  literalSelfPairDerivativeItem562
      D R S cutoff output outputNonzero tau outputExact = record
    { R422.pairCurve =
        pairCurve562 D R S cutoff output outputNonzero tau outputExact
    ; R422.cellADerivative =
        cellDerivative562 D R S cutoff output outputNonzero tau outputExact
    ; R422.cellBDerivative =
        cellDerivative562 D R S cutoff output outputNonzero tau outputExact
    }

round562OneLiteralSelfPairDerivativeItemConstructed : Bool
round562OneLiteralSelfPairDerivativeItemConstructed = true

round562CellADerivativeEqualsCellBDerivativeBySelfPair : Bool
round562CellADerivativeEqualsCellBDerivativeBySelfPair = true

round562NewDerivativeCalculusIntroduced : Bool
round562NewDerivativeCalculusIntroduced = false

round562FiniteSelfPairEnumerationStillOpen : Bool
round562FiniteSelfPairEnumerationStillOpen = true

round562ClayPromotion : Bool
round562ClayPromotion = false

round562OneLiteralSelfPairDerivativeItemConstructedIsTrue :
  round562OneLiteralSelfPairDerivativeItemConstructed ≡ true
round562OneLiteralSelfPairDerivativeItemConstructedIsTrue = refl

round562NewDerivativeCalculusIntroducedIsFalse :
  round562NewDerivativeCalculusIntroduced ≡ false
round562NewDerivativeCalculusIntroducedIsFalse = refl

round562ClayPromotionIsFalse : round562ClayPromotion ≡ false
round562ClayPromotionIsFalse = refl
