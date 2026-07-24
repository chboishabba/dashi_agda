module DASHI.Physics.YangMills.BalabanSU2RadialTrigAuthority where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; _*R_; oneR)
open import DASHI.Physics.YangMills.BalabanSU2AdjointTransportExact using
  (squareR; vectorNormSqR)
open import DASHI.Physics.YangMills.BalabanSU2AdjointOrderedReduction using
  (LessEqual)
open import DASHI.Physics.YangMills.BalabanSU2AdjointPointwiseRadiusSquared using
  (SU2AdjointSquaredRadiusOrderLaws; orderedSquares)
import DASHI.Physics.YangMills.BalabanSU2RadialExponentialChartExact as Chart

------------------------------------------------------------------------
-- Minimal authoritative trigonometric surface for the SU(2) radial chart.
--
-- No unrestricted trigonometry postulate is introduced here.  A concrete real
-- analysis backend must inhabit exactly these three public facts for its sine,
-- cosine and removable sin(t)/t implementation.
------------------------------------------------------------------------

record SU2RadialTrigAuthority : Set₁ where
  field
    sine cosine sinOverArgument : ℝ → ℝ

    sinOverArgumentAbsBelowOne : ∀ t →
      absℝ (sinOverArgument t) ≤ℝ 1ℝ

    sinCosPythagorean : ∀ t →
      squareR (cosine t) +R squareR (sine t) ≡ oneR

    sinOverArgumentAtZero :
      sinOverArgument 0ℝ ≡ 1ℝ

open SU2RadialTrigAuthority public

------------------------------------------------------------------------
-- Repository norm/radius bridge.
--
-- The first equality identifies |A|^2 with the radial parameter squared.  The
-- second is the definitional removable-quotient bridge needed to replace
-- (sin(t)/t)^2 t^2 by sin^2(t).  The order bridge consumes the authoritative
-- absolute-value bound and the chart-ball premise; it contains no further
-- trigonometric content.
------------------------------------------------------------------------

record SU2RadialParameterBridge
    (radius : ℝ)
    (trig : SU2RadialTrigAuthority) : Set₁ where
  field
    radialOrderLaws : SU2AdjointSquaredRadiusOrderLaws

    Parameter : Set
    parameterX parameterY parameterZ parameterRadius : Parameter → ℝ
    inChartBall : Parameter → Set

    vectorNormSqMatchesRadialParameterSq : ∀ parameter →
      vectorNormSqR
        (parameterX parameter)
        (parameterY parameter)
        (parameterZ parameter)
      ≡ squareR (parameterRadius parameter)

    sinOverArgumentSquareTimesParameterSq : ∀ parameter →
      squareR (sinOverArgument trig (parameterRadius parameter))
      *R squareR (parameterRadius parameter)
      ≡ squareR (sine trig (parameterRadius parameter))

    sinOverArgumentBoundAndRadiusBridge : ∀ parameter →
      inChartBall parameter →
      absℝ (sinOverArgument trig (parameterRadius parameter)) ≤ℝ 1ℝ →
      LessEqual (orderedSquares radialOrderLaws)
        (squareR (sinOverArgument trig (parameterRadius parameter))
          *R vectorNormSqR
            (parameterX parameter)
            (parameterY parameter)
            (parameterZ parameter))
        (squareR radius)

open SU2RadialParameterBridge public

trigRadialUnitIdentity :
  ∀ {radius} {trig : SU2RadialTrigAuthority}
    (bridge : SU2RadialParameterBridge radius trig)
    parameter →
  squareR (cosine trig (parameterRadius bridge parameter))
    +R (squareR (sinOverArgument trig (parameterRadius bridge parameter))
      *R vectorNormSqR
        (parameterX bridge parameter)
        (parameterY bridge parameter)
        (parameterZ bridge parameter))
  ≡ oneR
trigRadialUnitIdentity {trig = trig} bridge parameter =
  trans
    (cong
      (λ normSq →
        squareR (cosine trig (parameterRadius bridge parameter))
        +R (squareR
          (sinOverArgument trig (parameterRadius bridge parameter))
          *R normSq))
      (vectorNormSqMatchesRadialParameterSq bridge parameter))
    (trans
      (cong
        (λ imaginarySq →
          squareR (cosine trig (parameterRadius bridge parameter))
          +R imaginarySq)
        (sinOverArgumentSquareTimesParameterSq bridge parameter))
      (sinCosPythagorean trig (parameterRadius bridge parameter)))

trigRadialImaginarySqBelowRadiusSq :
  ∀ {radius} {trig : SU2RadialTrigAuthority}
    (bridge : SU2RadialParameterBridge radius trig)
    parameter →
  inChartBall bridge parameter →
  LessEqual (orderedSquares (radialOrderLaws bridge))
    (squareR (sinOverArgument trig (parameterRadius bridge parameter))
      *R vectorNormSqR
        (parameterX bridge parameter)
        (parameterY bridge parameter)
        (parameterZ bridge parameter))
    (squareR radius)
trigRadialImaginarySqBelowRadiusSq {trig = trig} bridge parameter inBall =
  sinOverArgumentBoundAndRadiusBridge bridge parameter inBall
    (sinOverArgumentAbsBelowOne trig (parameterRadius bridge parameter))

trigRadialExponentialChartData :
  ∀ {radius} {trig : SU2RadialTrigAuthority} →
  SU2RadialParameterBridge radius trig →
  Chart.SU2RadialExponentialChartData radius
trigRadialExponentialChartData {trig = trig} bridge = record
  { Chart.radialOrderLaws = radialOrderLaws bridge
  ; Chart.radialParameter = Parameter bridge
  ; Chart.radialParameterX = parameterX bridge
  ; Chart.radialParameterY = parameterY bridge
  ; Chart.radialParameterZ = parameterZ bridge
  ; Chart.radialCosine = λ parameter →
      cosine trig (parameterRadius bridge parameter)
  ; Chart.radialScale = λ parameter →
      sinOverArgument trig (parameterRadius bridge parameter)
  ; Chart.radialInChartBall = inChartBall bridge
  ; Chart.radialUnitIdentity = λ parameter inBall →
      trigRadialUnitIdentity bridge parameter
  ; Chart.radialImaginarySqBelowRadiusSq =
      trigRadialImaginarySqBelowRadiusSq bridge
  }

su2RadialTrigAuthoritySurfaceLevel : ProofLevel
su2RadialTrigAuthoritySurfaceLevel = machineChecked

su2RadialTrigToQuaternionChartLevel : ProofLevel
su2RadialTrigToQuaternionChartLevel = machineChecked

sinCosPythagoreanAuthorityLevel : ProofLevel
sinCosPythagoreanAuthorityLevel = conditional

sinOverArgumentAbsBelowOneAuthorityLevel : ProofLevel
sinOverArgumentAbsBelowOneAuthorityLevel = conditional

sinOverArgumentAtZeroAuthorityLevel : ProofLevel
sinOverArgumentAtZeroAuthorityLevel = conditional
