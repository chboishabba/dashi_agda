module DASHI.Analysis.RiemannQuarticSignedPoleJointHorizontalJetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RH G3 JOINT HORIZONTAL / ORDINATE JET OWNER
--
-- Lean companion:
--
--   Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean
--
-- The failed full-cubic discrepancy quotient does not exhaust the quartic
-- geometry.  The literal completed per-zero source keeps horizontal
-- displacement and ordinate displacement coupled.
--
-- For normalized coordinates
--
--   alpha = (beta - 1/2) / r
--   q     = (gamma - t) / r
--   r     = t/16
--
-- the exact signed pair kernel has the theorem-bearing normal form
--
--   K_W(alpha,q)
--     =
--   S(W) * (alpha^2 q^2 - q^4/6)
--     + R_joint(alpha,q).
--
-- On the literal physical zero carrier this becomes
--
--   m_rho * S(W) / r^6
--     * (a_rho^2 delta_rho^2 - delta_rho^4/6)
--     + literal R_joint.
--
-- The leading polynomial has a mixed sign cone:
--
--   delta^2 < 6 a^2  -> positive
--   delta^2 > 6 a^2  -> negative.
--
-- Therefore the horizontal jet is not a uniform-sign replacement for G3.
-- The next real analytic question is the same-object size/sign/cancellation
-- of R_joint after summation, without prematurely splitting N-mu from the
-- horizontal remainder.
------------------------------------------------------------------------

data JointHorizontalJetCoordinate : Set where
  literalJointPairSourceSameObject : JointHorizontalJetCoordinate
  horizontalQuadraticKernelZeroAtOrigin : JointHorizontalJetCoordinate
  horizontalQuadraticKernelFirstDerivativeZero : JointHorizontalJetCoordinate
  horizontalQuadraticKernelSecondDerivativeFourStrength :
    JointHorizontalJetCoordinate
  localHorizontalQuadraticGain : JointHorizontalJetCoordinate
  literalHorizontalTargetScale : JointHorizontalJetCoordinate

  exactJointQuarticPolynomial : JointHorizontalJetCoordinate
  exactJointQuarticRemainder : JointHorizontalJetCoordinate
  literalJointQuarticPhysicalScaling : JointHorizontalJetCoordinate
  jointQuarticPositiveCone : JointHorizontalJetCoordinate
  jointQuarticNegativeCone : JointHorizontalJetCoordinate

  jointRemainderUniformSign : JointHorizontalJetCoordinate
  jointRemainderSharpBound : JointHorizontalJetCoordinate
  summedJointQuarticMechanismClosesG3 : JointHorizontalJetCoordinate

data JointHorizontalJetStatus : Set where
  theoremOwned : JointHorizontalJetStatus
  openAnalyticObstruction : JointHorizontalJetStatus

jointHorizontalJetStatus :
  JointHorizontalJetCoordinate -> JointHorizontalJetStatus
jointHorizontalJetStatus literalJointPairSourceSameObject = theoremOwned
jointHorizontalJetStatus horizontalQuadraticKernelZeroAtOrigin = theoremOwned
jointHorizontalJetStatus horizontalQuadraticKernelFirstDerivativeZero = theoremOwned
jointHorizontalJetStatus
  horizontalQuadraticKernelSecondDerivativeFourStrength = theoremOwned
jointHorizontalJetStatus localHorizontalQuadraticGain = theoremOwned
jointHorizontalJetStatus literalHorizontalTargetScale = theoremOwned

jointHorizontalJetStatus exactJointQuarticPolynomial = theoremOwned
jointHorizontalJetStatus exactJointQuarticRemainder = theoremOwned
jointHorizontalJetStatus literalJointQuarticPhysicalScaling = theoremOwned
jointHorizontalJetStatus jointQuarticPositiveCone = theoremOwned
jointHorizontalJetStatus jointQuarticNegativeCone = theoremOwned

jointHorizontalJetStatus jointRemainderUniformSign = openAnalyticObstruction
jointHorizontalJetStatus jointRemainderSharpBound = openAnalyticObstruction
jointHorizontalJetStatus summedJointQuarticMechanismClosesG3 =
  openAnalyticObstruction

record QuarticSignedPoleJointHorizontalJetBoundary : Set where
  constructor quartic-signed-pole-joint-horizontal-jet-boundary
  field
    literalJointPairSourceSameObjectPaid : Bool
    horizontalQuadraticKernelZeroAtOriginPaid : Bool
    horizontalQuadraticKernelFirstDerivativeZeroPaid : Bool
    horizontalQuadraticKernelSecondDerivativeFourStrengthPaid : Bool
    localHorizontalQuadraticGainPaid : Bool
    literalHorizontalTargetScalePaid : Bool

    exactJointQuarticPolynomialPaid : Bool
    exactJointQuarticRemainderPaid : Bool
    literalJointQuarticPhysicalScalingPaid : Bool
    jointQuarticPositiveConePaid : Bool
    jointQuarticNegativeConePaid : Bool

    jointRemainderUniformSignPaid : Bool
    jointRemainderSharpBoundPaid : Bool
    summedJointQuarticMechanismClosesG3Paid : Bool

    literalJointPairSourceSameObjectPaidIsTrue :
      literalJointPairSourceSameObjectPaid ≡ true
    horizontalQuadraticKernelZeroAtOriginPaidIsTrue :
      horizontalQuadraticKernelZeroAtOriginPaid ≡ true
    horizontalQuadraticKernelFirstDerivativeZeroPaidIsTrue :
      horizontalQuadraticKernelFirstDerivativeZeroPaid ≡ true
    horizontalQuadraticKernelSecondDerivativeFourStrengthPaidIsTrue :
      horizontalQuadraticKernelSecondDerivativeFourStrengthPaid ≡ true
    localHorizontalQuadraticGainPaidIsTrue :
      localHorizontalQuadraticGainPaid ≡ true
    literalHorizontalTargetScalePaidIsTrue :
      literalHorizontalTargetScalePaid ≡ true

    exactJointQuarticPolynomialPaidIsTrue :
      exactJointQuarticPolynomialPaid ≡ true
    exactJointQuarticRemainderPaidIsTrue :
      exactJointQuarticRemainderPaid ≡ true
    literalJointQuarticPhysicalScalingPaidIsTrue :
      literalJointQuarticPhysicalScalingPaid ≡ true
    jointQuarticPositiveConePaidIsTrue :
      jointQuarticPositiveConePaid ≡ true
    jointQuarticNegativeConePaidIsTrue :
      jointQuarticNegativeConePaid ≡ true

    jointRemainderUniformSignPaidIsFalse :
      jointRemainderUniformSignPaid ≡ false
    jointRemainderSharpBoundPaidIsFalse :
      jointRemainderSharpBoundPaid ≡ false
    summedJointQuarticMechanismClosesG3PaidIsFalse :
      summedJointQuarticMechanismClosesG3Paid ≡ false

    interpretation : String
    nextResearchCut : String

canonicalQuarticSignedPoleJointHorizontalJetBoundary :
  QuarticSignedPoleJointHorizontalJetBoundary
canonicalQuarticSignedPoleJointHorizontalJetBoundary =
  quartic-signed-pole-joint-horizontal-jet-boundary
    true true true true true true
    true true true true true
    false false false
    refl refl refl refl refl refl
    refl refl refl refl refl
    refl refl refl
    "The exact literal G3 source now exposes a joint two-variable quartic jet rather than separate N-mu and horizontal estimates.  The normalized leading polynomial is S(W)*(alpha^2*q^2-q^4/6), and on the physical zero carrier it scales as m_rho*S(W)*(a^2*delta^2-delta^4/6)/r^6.  The horizontal quadratic coefficient has value and first derivative zero at q=0 and second derivative 4*S(W)>0.  This is a real fourth-order coupled mechanism, but it has a mixed sign cone rather than a uniform favorable sign."
    "Do not promote the horizontal jet to G3.  The next analytic cut is control of the exact same-object joint remainder, especially whether its summed contribution couples with the mixed quartic polynomial strongly enough to produce the strict completed-residual bound.  Preserve the failed full-cubic quotient as a diagnostic donor, not as an assumed cancellation."

jointQuarticPolynomialIsPaid :
  jointHorizontalJetStatus exactJointQuarticPolynomial ≡ theoremOwned
jointQuarticPolynomialIsPaid = refl

jointPositiveConeIsPaid :
  jointHorizontalJetStatus jointQuarticPositiveCone ≡ theoremOwned
jointPositiveConeIsPaid = refl

jointNegativeConeIsPaid :
  jointHorizontalJetStatus jointQuarticNegativeCone ≡ theoremOwned
jointNegativeConeIsPaid = refl

jointRemainderRemainsOpen :
  jointHorizontalJetStatus jointRemainderSharpBound ≡ openAnalyticObstruction
jointRemainderRemainsOpen = refl
