module DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxDerivativeRound564Exact where

------------------------------------------------------------------------
-- ROUND564 / PER-OUTPUT R563 DERIVATIVES -> LIVE GLOBAL SELF-FLUX DERIVATIVE
--
-- R563 closes the exact self-flux derivative on one nonzero output fibre.
-- R406/R556 use the fixed canonical nonzero output list at every time.  Finite
-- scalar derivative closure from R412 therefore lifts the R563 witnesses across
-- that SAME list, with no output-cardinality estimate and no new calculus.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNLiteralSelfFluxDerivativeClosedRound563Exact as R563
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module LiveGlobalDerivative
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) →
      (Time → ℚ) → Set)
    (projectedCrossCalculus :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarAlgebra : R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo VectorDerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo VectorDerivativeOf D))
    (cutoff : Nat) where

  outputs : List Z3.FourierMode
  outputs = Canonical.nonzeroCutoffModes cutoff

  canonicalNonzero :
    (output : Z3.FourierMode) →
    output Cube.∈ outputs → Z3.NonZeroMode output
  canonicalNonzero output member = R404.nonzeroCutoffMemberNonzero member

  outputFluxCurves :
    (selected : List Z3.FourierMode) →
    ((output : Z3.FourierMode) → output Cube.∈ selected → Z3.NonZeroMode output) →
    List (Time → ℚ)
  outputFluxCurves [] allNonzero = []
  outputFluxCurves (output ∷ rest) allNonzero =
    let
      module One = R563.ClosedDerivative
        Time initialTime integrateTo VectorDerivativeOf ScalarDerivativeOf
        projectedCrossCalculus vectorAlgebra hermitianCalculus constantCalculus
        scalarAlgebra D R cutoff output
        (allNonzero output (Cube.here refl))
    in
    One.Family.selfFlux ∷
      outputFluxCurves rest
        (λ selected member → allNonzero selected (Cube.there member))

  outputTangentCurves :
    (selected : List Z3.FourierMode) →
    ((output : Z3.FourierMode) → output Cube.∈ selected → Z3.NonZeroMode output) →
    List (Time → ℚ)
  outputTangentCurves [] allNonzero = []
  outputTangentCurves (output ∷ rest) allNonzero =
    let
      module One = R563.ClosedDerivative
        Time initialTime integrateTo VectorDerivativeOf ScalarDerivativeOf
        projectedCrossCalculus vectorAlgebra hermitianCalculus constantCalculus
        scalarAlgebra D R cutoff output
        (allNonzero output (Cube.here refl))
    in
    One.Family.selfFluxTangent ∷
      outputTangentCurves rest
        (λ selected member → allNonzero selected (Cube.there member))

  outputDerivatives :
    (selected : List Z3.FourierMode) →
    (allNonzero :
      (output : Z3.FourierMode) → output Cube.∈ selected → Z3.NonZeroMode output) →
    R412.AllDerivatives ScalarDerivativeOf
      (outputFluxCurves selected allNonzero)
      (outputTangentCurves selected allNonzero)
  outputDerivatives [] allNonzero = R412.derivativesNil
  outputDerivatives (output ∷ rest) allNonzero =
    let
      outputNN = allNonzero output (Cube.here refl)
      module One = R563.ClosedDerivative
        Time initialTime integrateTo VectorDerivativeOf ScalarDerivativeOf
        projectedCrossCalculus vectorAlgebra hermitianCalculus constantCalculus
        scalarAlgebra D R cutoff output outputNN
    in
    R412.derivativesCons
      One.literalSelfFluxDerivative
      (outputDerivatives rest
        (λ selected member → allNonzero selected (Cube.there member)))

  globalSelfFlux : Time → ℚ
  globalSelfFlux =
    R412.sumCurves (outputFluxCurves outputs canonicalNonzero)

  globalSelfFluxTangent : Time → ℚ
  globalSelfFluxTangent =
    R412.sumCurves (outputTangentCurves outputs canonicalNonzero)

  literalGlobalSelfFluxDerivative :
    ScalarDerivativeOf globalSelfFlux globalSelfFluxTangent
  literalGlobalSelfFluxDerivative =
    R412.finiteSumDerivative scalarAlgebra
      (outputDerivatives outputs canonicalNonzero)

round564PerOutputDerivativeAggregationClosed : Bool
round564PerOutputDerivativeAggregationClosed = true

round564GlobalSelfFluxDerivativeClosed : Bool
round564GlobalSelfFluxDerivativeClosed = true

round564OutputCardinalityEstimateIntroduced : Bool
round564OutputCardinalityEstimateIntroduced = false

round564NewDerivativeInterfaceIntroduced : Bool
round564NewDerivativeInterfaceIntroduced = false

round564OrdinaryScalarFTCStillRequired : Bool
round564OrdinaryScalarFTCStillRequired = true

round564FactoredFullSpacetimeBoundClosed : Bool
round564FactoredFullSpacetimeBoundClosed = false

round564CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round564CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round564ClayPromotion : Bool
round564ClayPromotion = false

round564GlobalSelfFluxDerivativeClosedIsTrue :
  round564GlobalSelfFluxDerivativeClosed ≡ true
round564GlobalSelfFluxDerivativeClosedIsTrue = refl

round564ClayPromotionIsFalse : round564ClayPromotion ≡ false
round564ClayPromotionIsFalse = refl
