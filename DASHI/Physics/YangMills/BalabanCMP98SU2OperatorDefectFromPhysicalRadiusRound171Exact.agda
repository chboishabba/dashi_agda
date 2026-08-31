{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98SU2OperatorDefectFromPhysicalRadiusRound171Exact where

------------------------------------------------------------------------
-- ROUND171 A1 BIDI: PHYSICAL RADIUS -> QUATERNION L1 -> OPERATOR DEFECT
--
-- Primary sources:
-- Tadeusz Bałaban, CMP 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Tadeusz Bałaban, CMP 102 (1985), 605--636. DOI: 10.1007/BF01229381.
-- Roger A. Horn and Charles R. Johnson, Matrix Analysis, 2nd ed. (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- The repository already proves, for the literal rational SU(2) carrier,
--
--   N(U^-1 - 1) <= 4 rho^2
--      -> ||U - 1||_1 <= 1/2048.
--
-- The only representation fact needed by CMP98 is the standard 2x2 SU(2)
-- estimate
--
--   ||U-I||_op <= ||coordinates(U-I)||_1.
--
-- This file keeps that standard matrix-analysis identification isolated, then
-- machine-checks the complete selected-link consequence.  Thus no caller is
-- allowed to supply the final 1/2048 operator bound directly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Op
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as QTelescope
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointNormSquaredExact as AdjointNorm
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanP33RelaxedRadiusQuaternionL1DefectExact as L1
import DASHI.Physics.YangMills.BalabanP33RelaxedRadiusQuaternionL1SharpExact as Sharp

record RationalSU2OperatorDefectRepresentation : Set₁ where
  field
    kernel : Op.UnitaryOperatorDefectKernel Q.RationalQuaternion

    operatorDefectBelowQuaternionL1 : ∀ value →
      Op.defect kernel value
      ≤ L1.quaternionDefectL1 (QTelescope._-q_ value Q.oneQ)

open RationalSU2OperatorDefectRepresentation public

positiveLinkNormSqBelowRelaxedRadius :
  ∀ background →
  Relaxed.RelaxedInverseLinkRadius background →
  ∀ bond →
  Norm.normSq
    (QTelescope._-q_ (Physical.link background bond) Q.oneQ)
  ≤ Relaxed.fourRhoSquare
positiveLinkNormSqBelowRelaxedRadius background radius bond =
  let
    inverseBound = radius bond
    sameNorm = AdjointNorm.inverseDifferenceNormSqExact
      (Physical.link background bond)
  in
  subst
    (λ lower → lower ≤ Relaxed.fourRhoSquare)
    sameNorm
    inverseBound

physicalPositiveLinkQuaternionL1BelowOne2048 :
  ∀ background →
  Relaxed.RelaxedInverseLinkRadius background →
  ∀ bond →
  L1.quaternionDefectL1
    (QTelescope._-q_ (Physical.link background bond) Q.oneQ)
  ≤ Budget.perLinkDefectMajorant
physicalPositiveLinkQuaternionL1BelowOne2048 background radius bond =
  let
    sharp = Sharp.relaxedNormSqImpliesSharpQuaternionL1Budget
      (QTelescope._-q_ (Physical.link background bond) Q.oneQ)
      (positiveLinkNormSqBelowRelaxedRadius background radius bond)
  in
  subst
    (λ upper →
      L1.quaternionDefectL1
        (QTelescope._-q_ (Physical.link background bond) Q.oneQ)
      ≤ upper)
    sharpBudgetIsPerLink
    sharp
  where
    sharpBudgetIsPerLink : Sharp.sharpL1Budget ≡ Budget.perLinkDefectMajorant
    sharpBudgetIsPerLink = refl

physicalPositiveLinkOperatorDefectBelowOne2048 :
  (representation : RationalSU2OperatorDefectRepresentation) →
  ∀ background →
  Relaxed.RelaxedInverseLinkRadius background →
  ∀ bond →
  Op.defect (kernel representation) (Physical.link background bond)
  ≤ Budget.perLinkDefectMajorant
physicalPositiveLinkOperatorDefectBelowOne2048 representation background radius bond =
  ℚP.≤-trans
    (operatorDefectBelowQuaternionL1 representation
      (Physical.link background bond))
    (physicalPositiveLinkQuaternionL1BelowOne2048 background radius bond)

cmp98PhysicalRadiusToQuaternionL1Round171Level : ProofLevel
cmp98PhysicalRadiusToQuaternionL1Round171Level = machineChecked

cmp98PhysicalRadiusToOperatorDefectRound171Level : ProofLevel
cmp98PhysicalRadiusToOperatorDefectRound171Level = machineChecked

cmp98RationalSU2OperatorRepresentationRound171Level : ProofLevel
cmp98RationalSU2OperatorRepresentationRound171Level = standardImported
