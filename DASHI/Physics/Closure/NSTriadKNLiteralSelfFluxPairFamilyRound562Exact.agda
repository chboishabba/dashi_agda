module DASHI.Physics.Closure.NSTriadKNLiteralSelfFluxPairFamilyRound562Exact where

------------------------------------------------------------------------
-- ROUND562 / ENUMERATE THE LITERAL SELF-PAIR DERIVATIVE FAMILY
--
-- R561 constructs one exact R422 PairCurveDerivativeData for every literal
-- self pair on the live R408 trajectory.  The physical output fibre is already
-- a fixed finite list independent of time.  This owner maps R561 over that
-- exact list and proves that the resulting R422 flux/tangent sums are the SAME
-- R549/R550 self-flux and self-flux-tangent observables.
--
-- Hence R559's former missingLiteralSelfPairCurveEnumeration559 is paid here.
-- No analytic estimate, cardinality bound, or second temporal semantics enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact as R422
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNPhysicalTrajectoryRetainedGlobalFluxRound403Exact as R403
import DASHI.Physics.Closure.NSTriadKNDiagonalSelfFluxToR447Round549Exact as R549
import DASHI.Physics.Closure.NSTriadKNLiteralDiagonalSumDecompositionRound550Exact as R550
import DASHI.Physics.Closure.NSTriadKNLiteralSelfFluxFiniteDerivativeCompilerRound559Exact as R559
import DASHI.Physics.Closure.NSTriadKNLiteralLiveSelfPairDerivativeRound561Exact as R561

F : C3.RealField _
F = Rational.rationalRealField

module LiteralSelfFluxFamily
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (crossCalculus : R426.ProjectedCrossDerivativeCalculus Time DerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time DerivativeOf)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo DerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo DerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo DerivativeOf D))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Literal = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Live = R403.LiveTrajectoryFlux
    Time initialTime integrateTo DerivativeOf

  T : R240.PhysicalNSDynamics.PhysicalNSGalerkinTrajectory
    Time initialTime integrateTo DerivativeOf
  T = Literal.literalPhysicalTrajectory D

  support : Live.RetainedSupportRealization T
  support = Support.toRetainedSupportRealization T R

  S = Literal.Base.S (Literal.stateTrajectory (Literal.support D))

  PS : Time → Field30.PhysicalFiniteComplex3GalerkinSystem F
  PS time = Live.physicalSystemAt T support cutoff time

  viscosityPositiveAt :
    (time : Time) → Positive (Field30.viscosity (PS time))
  viscosityPositiveAt time = Live.stateViscosityPositive T support cutoff time

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Output.physicalOutputFiber cutoff output

  module Rate0 = R400.PhysicalRate
    (PS initialTime) S (viscosityPositiveAt initialTime)

  allOutput :
    (alpha : Physical.PhysicalTriadIncidence) →
    alpha R396.OccursIn fibre → Physical.k alpha ≡ output
  allOutput = Rate0.allElementsHaveOutput cutoff output

  buildPairData :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    List (R422.PairCurveDerivativeData Time DerivativeOf)
  buildPairData [] itemOutput = []
  buildPairData (alpha ∷ rest) itemOutput =
    let
      module One = R561.LiteralSelfPairDerivative
        Time initialTime integrateTo DerivativeOf
        crossCalculus vectorAlgebra D R cutoff output outputNonzero
        alpha (itemOutput alpha R396.here)
    in
    One.literalSelfPairDerivativeData ∷
      buildPairData rest
        (λ beta member → itemOutput beta (R396.there member))

  pairCurves : List (R422.PairCurveDerivativeData Time DerivativeOf)
  pairCurves = buildPairData fibre allOutput

  selfFlux : Time → ℚ
  selfFlux time =
    let
      module Flux = R549.PhysicalSelfFlux
        (PS time) S (viscosityPositiveAt time)
        cutoff output outputNonzero
    in Flux.literalSelfFluxSum

  selfFluxTangent : Time → ℚ
  selfFluxTangent time =
    let
      module Diag = R550.LiteralDiagonal
        (PS time) S (viscosityPositiveAt time)
        cutoff output outputNonzero
    in Diag.literalSelfFluxTangentSum

  fluxSumExact :
    (items : List Physical.PhysicalTriadIncidence) →
    (itemOutput :
      (alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    (time : Time) →
    R412.sumCurves
      (R422.fluxTerms (buildPairData items itemOutput)) time
    ≡
    R549.PhysicalSelfFlux.sumSelfFlux
      (PS time) S (viscosityPositiveAt time)
      cutoff output outputNonzero items
      (λ alpha member → itemOutput alpha member)
  fluxSumExact [] itemOutput time = refl
  fluxSumExact (alpha ∷ rest) itemOutput time =
    cong₂ _+_ refl
      (fluxSumExact rest
        (λ beta member → itemOutput beta (R396.there member)) time)

  tangentSumExact :
    (items : List Physical.PhysicalTriadIncidence) →
    (itemOutput :
      (alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    (time : Time) →
    R412.sumCurves
      (R422.tangentTerms (buildPairData items itemOutput)) time
    ≡
    R550.LiteralDiagonal.sumSelfFluxTangent
      (PS time) S (viscosityPositiveAt time)
      cutoff output outputNonzero items
      (λ alpha member → itemOutput alpha member)
  tangentSumExact [] itemOutput time = refl
  tangentSumExact (alpha ∷ rest) itemOutput time =
    cong₂ _+_ refl
      (tangentSumExact rest
        (λ beta member → itemOutput beta (R396.there member)) time)

  literalSelfFluxFamily :
    R559.LiteralSelfFluxFiniteFamily559
      Time DerivativeOf selfFlux selfFluxTangent
  literalSelfFluxFamily = record
    { R559.pairCurves = pairCurves
    ; R559.fluxSumIsLiteralSelfFlux = fluxSumExact fibre allOutput
    ; R559.tangentSumIsLiteralSelfFluxTangent = tangentSumExact fibre allOutput
    }

round562LiteralSelfPairCurveEnumerationClosed : Bool
round562LiteralSelfPairCurveEnumerationClosed = true

round562FluxSumIsExactR549SelfFlux : Bool
round562FluxSumIsExactR549SelfFlux = true

round562TangentSumIsExactR550SelfFluxTangent : Bool
round562TangentSumIsExactR550SelfFluxTangent = true

round562IntroducesOutputCardinalityTax : Bool
round562IntroducesOutputCardinalityTax = false

round562IntroducesNewAnalyticEstimate : Bool
round562IntroducesNewAnalyticEstimate = false

round562OrdinaryScalarFTCStillRequired : Bool
round562OrdinaryScalarFTCStillRequired = true

round562ClayPromotion : Bool
round562ClayPromotion = false

round562LiteralSelfPairCurveEnumerationClosedIsTrue :
  round562LiteralSelfPairCurveEnumerationClosed ≡ true
round562LiteralSelfPairCurveEnumerationClosedIsTrue = refl

round562ClayPromotionIsFalse : round562ClayPromotion ≡ false
round562ClayPromotionIsFalse = refl
