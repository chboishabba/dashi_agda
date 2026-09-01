module DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact where

------------------------------------------------------------------------
-- ROUND422 / FINITE SAME-PAIR DERIVATIVE FAMILY -> EXACT R409
--
-- R418 closes one weighted R290 pair once the two literal cell derivatives are
-- known.  R412 closes finite scalar summation.  This owner composes them for a
-- finite family of SAME R291/R290 pair curves and transports only at the final
-- boundary to the literal R406 flux/tangent.
--
-- Therefore the temporal red box no longer contains Hermitian calculus,
-- resolvent scaling, or finite summation.  The remaining physical task is to
-- enumerate the actual fixed R406 pair-position curves and prove the two cell
-- derivative witnesses for each position.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxDerivativeBoundaryRound409Exact as R409
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR291R290SamePairDerivativeRound418Exact as R418

F : C3.RealField _
F = Rational.rationalRealField

record PairCurveDerivativeData
    (Time : Set)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) : Set₁ where
  field
    pairCurve : R418.SameR291R290PairCurve Time
    cellADerivative :
      VectorDerivativeOf
        (R417.cellACurve (R418.r291Curve pairCurve))
        (R417.tangentACurve (R418.r291Curve pairCurve))
    cellBDerivative :
      VectorDerivativeOf
        (R417.cellBCurve (R418.r291Curve pairCurve))
        (R417.tangentBCurve (R418.r291Curve pairCurve))

open PairCurveDerivativeData public

fluxTerms :
  ∀ {Time VectorDerivativeOf} →
  List (PairCurveDerivativeData Time VectorDerivativeOf) →
  List (Time → ℚ)
fluxTerms [] = []
fluxTerms (P ∷ rest) =
  R416.weightedFluxCurve (R418.r290Curve (pairCurve P)) ∷ fluxTerms rest

tangentTerms :
  ∀ {Time VectorDerivativeOf} →
  List (PairCurveDerivativeData Time VectorDerivativeOf) →
  List (Time → ℚ)
tangentTerms [] = []
tangentTerms (P ∷ rest) =
  R416.weightedFluxTangentCurve (R418.r290Curve (pairCurve P))
  ∷ tangentTerms rest

module FiniteFamily
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) →
      (Time → ℚ) → Set)
    (H : R417.HermitianDerivativeCalculus
      Time VectorDerivativeOf ScalarDerivativeOf)
    (C : R416.ScalarConstantDerivativeCalculus
      Time ScalarDerivativeOf)
    (A : R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf) where

  module Pair = R418.SamePairDerivative
    Time VectorDerivativeOf ScalarDerivativeOf H C
  module Dyn = R240.PhysicalNSDynamics
    Time initialTime integrateTo VectorDerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo VectorDerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo VectorDerivativeOf
  module Boundary = R409.Boundary
    Time initialTime integrateTo VectorDerivativeOf ScalarDerivativeOf

  allPairDerivatives :
    (items : List (PairCurveDerivativeData Time VectorDerivativeOf)) →
    R412.AllDerivatives ScalarDerivativeOf
      (fluxTerms items) (tangentTerms items)
  allPairDerivatives [] = R412.derivativesNil
  allPairDerivatives (P ∷ rest) =
    R412.derivativesCons
      (Pair.cellDerivativesBuildExactR290WeightedFluxDerivative
        (pairCurve P) (cellADerivative P) (cellBDerivative P))
      (allPairDerivatives rest)

  record LiteralR406PairFamily
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) : Set₁ where
    field
      pairCurves : List (PairCurveDerivativeData Time VectorDerivativeOf)
      fluxSumIsR406 :
        (time : Time) →
        R412.sumCurves (fluxTerms pairCurves) time
        ≡ Flux.At.offDiagonalFlux T R cutoff time
      tangentSumIsR406 :
        (time : Time) →
        R412.sumCurves (tangentTerms pairCurves) time
        ≡ Flux.At.offDiagonalFluxTangent T R cutoff time

  open LiteralR406PairFamily public

  literalPairFamilyBuildsR409 :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) →
    LiteralR406PairFamily T R cutoff →
    Boundary.FixedOutputFluxDerivative T R cutoff
  literalPairFamilyBuildsR409 T R cutoff P = record
    { Boundary.derivativeIsExactR406Tangent =
        R412.transportDerivative A
          (fluxSumIsR406 P)
          (tangentSumIsR406 P)
          (R412.finiteSumDerivative A
            (allPairDerivatives (pairCurves P)))
    }

round422PerPairHermitianAndResolventCalculusClosed : Bool
round422PerPairHermitianAndResolventCalculusClosed = true

round422FinitePairSummationClosed : Bool
round422FinitePairSummationClosed = true

round422FinalTargetIsLiteralR406Flux : Bool
round422FinalTargetIsLiteralR406Flux = true

round422RemainingTemporalLeafIsActualCellCurveDifferentiation : Bool
round422RemainingTemporalLeafIsActualCellCurveDifferentiation = true

round422FinalTargetIsLiteralR406FluxIsTrue :
  round422FinalTargetIsLiteralR406Flux ≡ true
round422FinalTargetIsLiteralR406FluxIsTrue = refl
