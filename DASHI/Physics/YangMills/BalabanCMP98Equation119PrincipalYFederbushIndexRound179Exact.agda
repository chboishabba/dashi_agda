{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PrincipalYFederbushIndexRound179Exact where

------------------------------------------------------------------------
-- ROUND179 A1 BIDI: THERE IS NO PRINCIPAL-Y/FEDERBUSH-Y IDENTIFICATION SEAM
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Commun. Math. Phys. 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Round178's frontier comment still described a possible identification
-- between the principal coordinate produced by the literal CMP98 relative
-- holonomy and the Y indexing the old Federbush calculus.  BIDI inspection
-- shows that this is not a physical theorem at all: Round177's convention is
-- a FAMILY indexed by every literal SU2LieAlgebra value.
--
-- Therefore the exact CMP98 point coordinate
--
--   Y_x = principalLog(U(Gamma_{c,x}) U(c)^-1)
--
-- is simply used as the argument of `atY`.  The same is true of the outer
-- block-average Y.  No equality receipt can intervene between the source Y and
-- the convention selected for that Y.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119YIndexedDexpRound154Exact as R154
import DASHI.Physics.YangMills.BalabanCMP98Equation119ExistingPrincipalLogRound156Exact as R156
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanCMP109PhysicalFederbushConventionCancellationExact as Federbush

pointPrincipalY :
  ∀ {n Group group Radius}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group) →
  Log.StandardSU2PrincipalLogBall Lie.SU2LieAlgebra Group Radius →
  Nat → Centered.CenteredBlockPoint4 6 → Lie.SU2LieAlgebra
pointPrincipalY source chart =
  R156.principalPointY (R158.asRound152Source source) chart

pointFederbushConvention :
  ∀ {n Group group Radius}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group)
    (chart : Log.StandardSU2PrincipalLogBall Lie.SU2LieAlgebra Group Radius) →
  R177.ExistingFederbushConventionFamily →
  Nat → Centered.CenteredBlockPoint4 6 →
  Federbush.LiteralCMP109FederbushConvention
    (pointPrincipalY source chart)
pointFederbushConvention source chart family step point =
  R177.atY family (pointPrincipalY source chart step point)

pointConventionIndexIsLiteralPrincipalY :
  ∀ {n Group group Radius}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group)
    (chart : Log.StandardSU2PrincipalLogBall Lie.SU2LieAlgebra Group Radius)
    (family : R177.ExistingFederbushConventionFamily)
    step point →
  pointFederbushConvention source chart family step point
  ≡ R177.atY family
      (R156.principalPointY
        (R158.asRound152Source source) chart step point)
pointConventionIndexIsLiteralPrincipalY source chart family step point = refl

pointJminusIsExistingFederbushAtLiteralPrincipalY :
  ∀ {n Group group Radius}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group)
    (chart : Log.StandardSU2PrincipalLogBall Lie.SU2LieAlgebra Group Radius)
    (family : R177.ExistingFederbushConventionFamily)
    step point variation →
  R177.R159.jMinusAt
    (R177.asUniformAdjointDifferentialCalculus family)
    (pointPrincipalY source chart step point) variation
  ≡ R177.R.applyReducedAdjoint
      (pointPrincipalY source chart step point)
      (Federbush.inverseMinus
        (pointFederbushConvention source chart family step point))
      variation
pointJminusIsExistingFederbushAtLiteralPrincipalY
    source chart family step point variation =
  R177.r159JminusIsExistingFederbushInverseMinus family
    (pointPrincipalY source chart step point) variation

pointAdjointIsExistingFederbushAtLiteralPrincipalY :
  ∀ {n Group group Radius}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group)
    (chart : Log.StandardSU2PrincipalLogBall Lie.SU2LieAlgebra Group Radius)
    (family : R177.ExistingFederbushConventionFamily)
    step point variation →
  R177.R159.adjointExp
    (R177.asUniformAdjointDifferentialCalculus family)
    (pointPrincipalY source chart step point) variation
  ≡ R177.R.applyReducedAdjoint
      (pointPrincipalY source chart step point)
      (Federbush.adjointTransport
        (pointFederbushConvention source chart family step point))
      variation
pointAdjointIsExistingFederbushAtLiteralPrincipalY
    source chart family step point variation =
  R177.r159AdjointIsExistingFederbushTransport family
    (pointPrincipalY source chart step point) variation

-- The outer coordinate is already generated by Round154 from the exact same
-- principal point family, so it too is passed directly to the uniform family.
outerPrincipalY :
  ∀ {n Group group Radius}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group) →
  Log.StandardSU2PrincipalLogBall Lie.SU2LieAlgebra Group Radius →
  Nat → Lie.SU2LieAlgebra
outerPrincipalY source chart step =
  R154.outerY
    (R158.asRound152Source source)
    (R156.asExistingPrincipalPointYFamily
      (R158.asRound152Source source) chart)
    step

outerFederbushConvention :
  ∀ {n Group group Radius}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group)
    (chart : Log.StandardSU2PrincipalLogBall Lie.SU2LieAlgebra Group Radius) →
  R177.ExistingFederbushConventionFamily → Nat →
  Federbush.LiteralCMP109FederbushConvention
    (outerPrincipalY source chart)
outerFederbushConvention source chart family step =
  R177.atY family (outerPrincipalY source chart step)

outerConventionIndexIsLiteralBlockAverageY :
  ∀ {n Group group Radius}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group)
    (chart : Log.StandardSU2PrincipalLogBall Lie.SU2LieAlgebra Group Radius)
    (family : R177.ExistingFederbushConventionFamily)
    step →
  outerFederbushConvention source chart family step
  ≡ R177.atY family
      (R154.outerY
        (R158.asRound152Source source)
        (R156.asExistingPrincipalPointYFamily
          (R158.asRound152Source source) chart)
        step)
outerConventionIndexIsLiteralBlockAverageY source chart family step = refl

cmp98Equation119PrincipalYFederbushIndexRound179Level : ProofLevel
cmp98Equation119PrincipalYFederbushIndexRound179Level = machineChecked

cmp98Equation119OuterYFederbushIndexRound179Level : ProofLevel
cmp98Equation119OuterYFederbushIndexRound179Level = machineChecked

-- There is no longer a `principal Y = Federbush Y` source seam.  The remaining
-- source-facing normalizations are the physical selected-background/kernel
-- realization, principal-chart admission/cut realization, the printed
-- `(1/i)log` coordinate convention, and the coarse-bond axis/orientation.
literalCMP98RemainingPhysicalNormalizationsRound179Level : ProofLevel
literalCMP98RemainingPhysicalNormalizationsRound179Level = conditional
