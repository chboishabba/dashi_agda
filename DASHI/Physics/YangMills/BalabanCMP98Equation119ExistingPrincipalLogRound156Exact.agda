{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119ExistingPrincipalLogRound156Exact where

------------------------------------------------------------------------
-- ROUND156 A1 BIDI: FORCE ROUND155 THROUGH THE EXISTING PRINCIPAL-LOG OWNER
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations", 2nd ed.,
-- Springer, 2015. DOI: 10.1007/978-3-319-13467-3.
--
-- Round155 removed the point-indexed Y_x receipt but still accepted one total
-- `logOverI : Group -> Lie` function.  That is still replaceable source data.
-- The repository already owns the SU(2) principal chart in
-- `BalabanClayGate4SU2PrincipalLogBallExact`, including branch uniqueness,
-- exp/log inverse laws, inverse orientation, and a physical transported-relative
-- bond interface.
--
-- This file makes THAT chart the actual Eq. (119) producer.  The only additional
-- source fact needed for a concrete background is admission of the literal
-- Round155 relative contour element to the selected principal image.  Once
-- admitted, exp(principalLog(relative)) = relative is inherited verbatim from
-- the existing owner.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP98Equation119YIndexedDexpRound154Exact as R154
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered

------------------------------------------------------------------------
-- Existing principal chart -> Round155 uniform log semantics.
--
-- Repository convention: `Log.principalLog` already lands in the Lie coordinate
-- consumed by expSU2.  The physical CMP98 normalization identifying this with
-- `(1/i) log` is kept as the source-normalization seam below, rather than hidden
-- in a fresh function.
------------------------------------------------------------------------

existingPrincipalLogSemantics :
  ∀ {Lie Group Radius} →
  Log.StandardSU2PrincipalLogBall Lie Group Radius →
  R155.CMP98PrincipalLogOverI Group Lie
existingPrincipalLogSemantics chart = record
  { R155.CMP98PrincipalLogOverI.logOverI = Log.principalLog chart }

record RelativeContourPrincipalImage
    {C n Group group Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group)
    (chart : Log.StandardSU2PrincipalLogBall
      (R126.Vector (R146.additive C)) Group Radius) : Set₁ where
  field
    relativeInImage : ∀ step (point : Centered.CenteredBlockPoint4 6) →
      Log.InPrincipalImage chart (R155.relativeContourElement source step point)

open RelativeContourPrincipalImage public

------------------------------------------------------------------------
-- Exact Y_x from the existing chart.
------------------------------------------------------------------------

principalPointY :
  ∀ {C n Group group Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group) →
  Log.StandardSU2PrincipalLogBall
    (R126.Vector (R146.additive C)) Group Radius →
  Nat → Centered.CenteredBlockPoint4 6 →
  R126.Vector (R146.additive C)
principalPointY source chart =
  R155.derivedPointY source (existingPrincipalLogSemantics chart)

principalPointYIsExistingPrincipalLog :
  ∀ {C n Group group Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group)
    (chart : Log.StandardSU2PrincipalLogBall
      (R126.Vector (R146.additive C)) Group Radius)
    step point →
  principalPointY source chart step point
  ≡ Log.principalLog chart (R155.relativeContourElement source step point)
principalPointYIsExistingPrincipalLog source chart step point = refl

principalPointYExponentiatesToLiteralRelativeContour :
  ∀ {C n Group group Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group)
    (chart : Log.StandardSU2PrincipalLogBall
      (R126.Vector (R146.additive C)) Group Radius)
    (admission : RelativeContourPrincipalImage source chart)
    step point →
  Log.expSU2 chart (principalPointY source chart step point)
  ≡ R155.relativeContourElement source step point
principalPointYExponentiatesToLiteralRelativeContour
    source chart admission step point =
  Log.expPrincipalLog chart
    (R155.relativeContourElement source step point)
    (relativeInImage admission step point)

asExistingPrincipalPointYFamily :
  ∀ {C n Group group Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group) →
  Log.StandardSU2PrincipalLogBall
    (R126.Vector (R146.additive C)) Group Radius →
  R154.CMP98Equation119PointYFamily source
asExistingPrincipalPointYFamily source chart =
  R155.asDerivedPointYFamily source (existingPrincipalLogSemantics chart)

existingPrincipalLogOneStepDerivative :
  ∀ {C n Group group Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group) →
  Log.StandardSU2PrincipalLogBall
    (R126.Vector (R146.additive C)) Group Radius →
  R154.UniformLeftRightDexpFamily (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
existingPrincipalLogOneStepDerivative source chart calculus =
  R154.yIndexedLeastPrivilegeOneStepDerivative
    source (asExistingPrincipalPointYFamily source chart) calculus

existingPrincipalLogMultiscaleDerivative :
  ∀ {C n Group group Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group) →
  Log.StandardSU2PrincipalLogBall
    (R126.Vector (R146.additive C)) Group Radius →
  R154.UniformLeftRightDexpFamily (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
existingPrincipalLogMultiscaleDerivative source chart calculus =
  R154.yIndexedLeastPrivilegeMultiscaleDerivative
    source (asExistingPrincipalPointYFamily source chart) calculus

cmp98Equation119ExistingPrincipalLogRound156Level : ProofLevel
cmp98Equation119ExistingPrincipalLogRound156Level = machineChecked

cmp98Equation119PrincipalLogExpRelativeContourRound156Level : ProofLevel
cmp98Equation119PrincipalLogExpRelativeContourRound156Level = machineChecked

-- Remaining physical seams after Round156:
--   * prove the literal relative contour elements lie in the selected principal
--     image from the already-owned CMP98 small-field/radius estimates;
--   * identify the repository Lie coordinate of this existing chart with
--     CMP98's printed `(1/i) log` normalization;
--   * use the same Y value to instantiate the existing LR/dexp family.
-- No independent log function or pointwise Y_x value remains.
literalCMP98RelativeContourPrincipalImageRound156Level : ProofLevel
literalCMP98RelativeContourPrincipalImageRound156Level = conditional

literalCMP98PrincipalLogOverINormalizationRound156Level : ProofLevel
literalCMP98PrincipalLogOverINormalizationRound156Level = conditional

literalCMP98UniformDexpAtPrincipalYRound156Level : ProofLevel
literalCMP98UniformDexpAtPrincipalYRound156Level = conditional
