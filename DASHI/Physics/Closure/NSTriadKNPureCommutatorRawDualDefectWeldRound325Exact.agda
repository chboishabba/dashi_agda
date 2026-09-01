module DASHI.Physics.Closure.NSTriadKNPureCommutatorRawDualDefectWeldRound325Exact where

------------------------------------------------------------------------
-- ROUND325 / R120 PURE COMMUTATOR = (-i) * P(output) * R172 RAW KERNEL
--
-- R324 proves on the literal C3 carrier
--
--   rotationalPair(a,b) = i * rawDirectionalSlotKernel(a,b).
--
-- R106 proves for helical inputs
--
--   rotationalPair(a,b) = (lambda_a-lambda_b) (u_a x u_b),
--
-- and R120's physical paired Galerkin vector is
--
--   (lambda_b-lambda_a) P_p(u_a x u_b).
--
-- Project the first equality through Leray, negate it, and use -i*i = 1 at
-- the scalar-sign level.  The result is the exact same-object identity
--
--   R120.pureCommutatorVector
--     = (-i) P_p(rawDirectionalSlotKernel).
--
-- This bypasses R232's still-open helical-basis/angular-symbol weld.  The
-- remaining analytic task is now to instantiate the R172--R177 dual-defect
-- norm geometry on this projected inner carrier and aggregate it shellwise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNConvectiveRotationalTriadIdentityRound93Exact as Conv
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as Scalar
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact as R120
import DASHI.Physics.Closure.NSTriadKNHHDualDefectRawCurlKernelRound172Exact as R172
import DASHI.Physics.Closure.NSTriadKNRotationalPairRawDirectionalRound324Exact as R324

complex3NegateScale :
  ∀ {r} {F : C3.RealField r}
    (s : C3.Complex F) (v : C3.Complex3 F) →
  C3.complex3Negate (C3.complex3Scale s v)
  ≡ C3.complex3Scale (C3.complexNegate s) v
complex3NegateScale {F = F} s (C3.complex3 x y z) =
  Field.complex3Ext
    (R.solve 2 (λ s x → R.⊝ (s R.⊗ x) R.⊜ (R.⊝ s) R.⊗ x) refl s x)
    (R.solve 2 (λ s y → R.⊝ (s R.⊗ y) R.⊜ (R.⊝ s) R.⊗ y) refl s y)
    (R.solve 2 (λ s z → R.⊝ (s R.⊗ z) R.⊜ (R.⊝ s) R.⊗ z) refl s z)
  where module R = Ring.Solver F

pureCommutatorIsMinusIProjectedRawKernel :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (H : R120.PhysicalHelicalOutputPair system tau) →
  R120.pureCommutatorVector system tau H
  ≡
  C3.complex3Scale (R106.minusI F)
    (C3.lerayProject3 E I (Physical.k tau)
      (R172.rawDirectionalSlotKernel
        (C3.modeVector E (Physical.p tau))
        (C3.modeVector E (Physical.q tau))
        (Audit.velocity system (Physical.p tau))
        (Audit.velocity system (Physical.q tau))))
pureCommutatorIsMinusIProjectedRawKernel {F = F} {E = E} {I = I}
    system tau H =
  let
    D = R120.asRound106Data H
    p = Physical.p tau
    q = Physical.q tau
    k = Physical.k tau
    uP = Audit.velocity system p
    uQ = Audit.velocity system q
    X = Cross.complex3Cross uP uQ
    raw = R172.rawDirectionalSlotKernel
      (C3.modeVector E p) (C3.modeVector E q) uP uQ
    deltaPQ = C3.complexSubtract (R120.signedEigenP H) (R120.signedEigenQ H)
    deltaQP = C3.complexSubtract (R120.signedEigenQ H) (R120.signedEigenP H)
    projectedX = C3.lerayProject3 E I k X
    projectedRaw = C3.lerayProject3 E I k raw

    rotationalToHelical :
      Conv.rotationalPair
        (C3.modeVector E p) (C3.modeVector E q) uP uQ
      ≡ C3.complex3Scale deltaPQ X
    rotationalToHelical = R106.projectedRotationalHelicalFactor D

    rotationalToRaw :
      Conv.rotationalPair
        (C3.modeVector E p) (C3.modeVector E q) uP uQ
      ≡ C3.complex3Scale (C3.complexI F) raw
    rotationalToRaw =
      R324.rotationalPairIsIRawDirectionalSlotKernel
        (C3.modeVector E p) (C3.modeVector E q) uP uQ

    helicalEqualsRaw :
      C3.complex3Scale deltaPQ X
      ≡ C3.complex3Scale (C3.complexI F) raw
    helicalEqualsRaw = trans (sym rotationalToHelical) rotationalToRaw

    projectedEquality :
      C3.complex3Scale deltaPQ projectedX
      ≡ C3.complex3Scale (C3.complexI F) projectedRaw
    projectedEquality =
      trans
        (sym (Scalar.lerayProjectComplexScale E I k deltaPQ X))
        (trans
          (cong (C3.lerayProject3 E I k) helicalEqualsRaw)
          (Scalar.lerayProjectComplexScale E I k (C3.complexI F) raw))

    leftNegate :
      C3.complex3Negate (C3.complex3Scale deltaPQ projectedX)
      ≡ C3.complex3Scale deltaQP projectedX
    leftNegate =
      trans
        (complex3NegateScale deltaPQ projectedX)
        (cong
          (λ scalar → C3.complex3Scale scalar projectedX)
          (R106.negateSubtractSwap
            (R120.signedEigenP H) (R120.signedEigenQ H)))

    rightNegate :
      C3.complex3Negate
        (C3.complex3Scale (C3.complexI F) projectedRaw)
      ≡ C3.complex3Scale (R106.minusI F) projectedRaw
    rightNegate = complex3NegateScale (C3.complexI F) projectedRaw

    desired :
      C3.complex3Scale deltaQP projectedX
      ≡ C3.complex3Scale (R106.minusI F) projectedRaw
    desired =
      trans
        (sym leftNegate)
        (trans
          (cong C3.complex3Negate projectedEquality)
          rightNegate)
  in desired

round325R120PureCommutatorWeldedToR172RawKernel : Bool
round325R120PureCommutatorWeldedToR172RawKernel = true

round325UsesR232PhysicalAngularBasisWeld : Bool
round325UsesR232PhysicalAngularBasisWeld = false

round325PhysicalInnerDualDefectNormPaymentClosed : Bool
round325PhysicalInnerDualDefectNormPaymentClosed = false

round325NestedHeatSchurClosed : Bool
round325NestedHeatSchurClosed = false

round325PackageAClosed : Bool
round325PackageAClosed = false

round325ClayPromotion : Bool
round325ClayPromotion = false

round325PackageAClosedIsFalse : round325PackageAClosed ≡ false
round325PackageAClosedIsFalse = refl

round325ClayPromotionIsFalse : round325ClayPromotion ≡ false
round325ClayPromotionIsFalse = refl
