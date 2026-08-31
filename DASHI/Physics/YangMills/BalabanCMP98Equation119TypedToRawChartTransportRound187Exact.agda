{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119TypedToRawChartTransportRound187Exact where

------------------------------------------------------------------------
-- ROUND187 A1 BIDI: KEEP PATH ALGEBRA TYPED; FORGET ONLY AT THE RAW CHART
--
-- Round186 constructs the physical periodic bond realization on the correct
-- `RationalUnitQuaternion` carrier.  The older selected principal chart is
-- formulated on raw quaternion coordinates.  Rather than invent a second
-- exponential theorem on the typed carrier, transport only the group element
-- presented to that chart.
--
-- The forgetful map is exactly a homomorphism for identity, multiplication and
-- inverse.  Thus a typed path/relative product can be evaluated by the existing
-- raw principal chart without changing its group word or ordering.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Unit
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Raw
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanCMP98Equation119TypedPhysicalRealizationRound186Exact as R186

forgetIdentity :
  R186.forgetUnitQuaternion Group.identityRationalSU2
  ≡ Raw.oneQ
forgetIdentity = refl

forgetMultiply : ∀ left right →
  R186.forgetUnitQuaternion (Group.multiplyRationalSU2 left right)
  ≡ Raw._*q_
      (R186.forgetUnitQuaternion left)
      (R186.forgetUnitQuaternion right)
forgetMultiply left right = refl

forgetInverse : ∀ value →
  R186.forgetUnitQuaternion (Group.inverseRationalSU2 value)
  ≡ Raw.quat
      (Raw.q0 (R186.forgetUnitQuaternion value))
      (- Raw.q1 (R186.forgetUnitQuaternion value))
      (- Raw.q2 (R186.forgetUnitQuaternion value))
      (- Raw.q3 (R186.forgetUnitQuaternion value))
forgetInverse value = refl

record RawPrincipalChartOnTypedCarrier (Lie Radius : Set) : Set₁ where
  field
    rawChart : Log.StandardSU2PrincipalLogBall
      Lie Raw.RationalQuaternion Radius

open RawPrincipalChartOnTypedCarrier public

typedPrincipalLog :
  ∀ {Lie Radius} →
  RawPrincipalChartOnTypedCarrier Lie Radius →
  Unit.RationalUnitQuaternion → Lie
typedPrincipalLog chart value =
  Log.principalLog (rawChart chart) (R186.forgetUnitQuaternion value)

asCMP98PrincipalLogOverI :
  ∀ {Lie Radius} →
  RawPrincipalChartOnTypedCarrier Lie Radius →
  R155.CMP98PrincipalLogOverI Unit.RationalUnitQuaternion Lie
asCMP98PrincipalLogOverI chart = record
  { R155.CMP98PrincipalLogOverI.logOverI = typedPrincipalLog chart }

typedPrincipalLogIsRawSelectedPrincipalLog :
  ∀ {Lie Radius}
    (chart : RawPrincipalChartOnTypedCarrier Lie Radius)
    value →
  R155.logOverI (asCMP98PrincipalLogOverI chart) value
  ≡ Log.principalLog (rawChart chart)
      (R186.forgetUnitQuaternion value)
typedPrincipalLogIsRawSelectedPrincipalLog chart value = refl

cmp98Equation119TypedToRawChartTransportRound187Level : ProofLevel
cmp98Equation119TypedToRawChartTransportRound187Level = machineChecked

cmp98Equation119ForgetfulGroupWordExactRound187Level : ProofLevel
cmp98Equation119ForgetfulGroupWordExactRound187Level = machineChecked

-- Remaining source-faithful chart leaf is now only principal-image admission
-- of the forgotten ACTUAL typed relative product in the already-selected raw
-- chart.  No global raw-quaternion group structure and no typed exponential
-- closure theorem are required.
literalCMP98ForgottenRelativePrincipalImageRound187Level : ProofLevel
literalCMP98ForgottenRelativePrincipalImageRound187Level = conditional
