{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PhysicalPrincipalImageRound157Exact where

------------------------------------------------------------------------
-- ROUND157 A1 BIDI: PRINCIPAL-IMAGE ADMISSION FROM THE EXISTING PHYSICAL OWNER
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- Round156 forced Eq. (119) through the repository's existing SU(2) principal
-- logarithm, but still accepted a fresh pointwise proof that every literal
-- relative contour element lies in the principal image.
--
-- The principal-log owner already has the stronger physical theorem:
-- a PhysicalSmallField configuration sends every selected transported relative
-- bond to the principal image.  BIDI therefore says not to prove image
-- membership again.  Instead identify the SAME literal Eq. (119) relative
-- contour with that already-owned transported-relative object.
--
-- This file makes that reduction exact.  Once a scale-indexed physical field,
-- coarse bond and fine point are identified and the transported relative object
-- is proved equal to Round155's actual path-holonomy product, principal-image
-- admission is inherited by equality transport.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP98Equation119YIndexedDexpRound154Exact as R154
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanCMP98Equation119ExistingPrincipalLogRound156Exact as R156
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered

------------------------------------------------------------------------
-- SAME-OBJECT bridge only.  It does not contain a principal-image proof.
------------------------------------------------------------------------

record CMP98RelativeContourPhysicalBridge
    {C n Group group Field CoarseBond FineBond Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group)
    (meaning : Log.PhysicalSU2PrincipalLogMeaning
      Field CoarseBond FineBond
      (R126.Vector (R146.additive C)) Group Radius) : Set₁ where
  field
    fieldAtStep : Nat → Field
    coarseAtStep : Nat → CoarseBond
    fineAtPoint : Nat → Centered.CenteredBlockPoint4 6 → FineBond

    physicalSmallFieldAtStep : ∀ step →
      Log.PhysicalSmallField meaning (fieldAtStep step)

    -- This is the only geometric same-object weld needed here.  The LHS is the
    -- transported relative object already controlled by the principal-log owner;
    -- the RHS is Round155's literal pathHolonomy(Gamma) * pathHolonomy(c)^-1.
    transportedRelativeIsLiteralContour : ∀ step point →
      Log.transportedRelativeBond meaning
        (fieldAtStep step)
        (coarseAtStep step)
        (fineAtPoint step point)
      ≡ R155.relativeContourElement source step point

open CMP98RelativeContourPhysicalBridge public

------------------------------------------------------------------------
-- Pointwise principal-image admission is now DERIVED, not supplied.
------------------------------------------------------------------------

relativeContourInPrincipalImage :
  ∀ {C n Group group Field CoarseBond FineBond Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group)
    (meaning : Log.PhysicalSU2PrincipalLogMeaning
      Field CoarseBond FineBond
      (R126.Vector (R146.additive C)) Group Radius)
    (bridge : CMP98RelativeContourPhysicalBridge source meaning)
    step point →
  Log.InPrincipalImage (Log.chart meaning)
    (R155.relativeContourElement source step point)
relativeContourInPrincipalImage source meaning bridge step point =
  subst
    (Log.InPrincipalImage (Log.chart meaning))
    (transportedRelativeIsLiteralContour bridge step point)
    (Log.smallFieldImage meaning
      (fieldAtStep bridge step)
      (physicalSmallFieldAtStep bridge step)
      (coarseAtStep bridge step)
      (fineAtPoint bridge step point))

asRound156PrincipalImage :
  ∀ {C n Group group Field CoarseBond FineBond Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group)
    (meaning : Log.PhysicalSU2PrincipalLogMeaning
      Field CoarseBond FineBond
      (R126.Vector (R146.additive C)) Group Radius) →
  CMP98RelativeContourPhysicalBridge source meaning →
  R156.RelativeContourPrincipalImage source (Log.chart meaning)
asRound156PrincipalImage source meaning bridge = record
  { R156.RelativeContourPrincipalImage.relativeInImage =
      relativeContourInPrincipalImage source meaning bridge
  }

------------------------------------------------------------------------
-- The physical log and Eq. (119) Y_x are now the SAME value.
------------------------------------------------------------------------

physicalLogEqualsPrincipalPointY :
  ∀ {C n Group group Field CoarseBond FineBond Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group)
    (meaning : Log.PhysicalSU2PrincipalLogMeaning
      Field CoarseBond FineBond
      (R126.Vector (R146.additive C)) Group Radius)
    (bridge : CMP98RelativeContourPhysicalBridge source meaning)
    step point →
  Log.physicalLog meaning
    (fieldAtStep bridge step)
    (coarseAtStep bridge step)
    (fineAtPoint bridge step point)
  ≡ R156.principalPointY source (Log.chart meaning) step point
physicalLogEqualsPrincipalPointY source meaning bridge step point =
  trans
    (Log.physicalLogMeaning meaning
      (fieldAtStep bridge step)
      (coarseAtStep bridge step)
      (fineAtPoint bridge step point))
    (cong
      (Log.principalLog (Log.chart meaning))
      (transportedRelativeIsLiteralContour bridge step point))

principalPointYExponentiatesByPhysicalSmallField :
  ∀ {C n Group group Field CoarseBond FineBond Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group)
    (meaning : Log.PhysicalSU2PrincipalLogMeaning
      Field CoarseBond FineBond
      (R126.Vector (R146.additive C)) Group Radius)
    (bridge : CMP98RelativeContourPhysicalBridge source meaning)
    step point →
  Log.expSU2 (Log.chart meaning)
    (R156.principalPointY source (Log.chart meaning) step point)
  ≡ R155.relativeContourElement source step point
principalPointYExponentiatesByPhysicalSmallField source meaning bridge step point =
  R156.principalPointYExponentiatesToLiteralRelativeContour
    source (Log.chart meaning)
    (asRound156PrincipalImage source meaning bridge)
    step point

------------------------------------------------------------------------
-- Direct downstream Eq. (119) producer from the physical principal-log owner.
------------------------------------------------------------------------

physicalPrincipalImageOneStepDerivative :
  ∀ {C n Group group Field CoarseBond FineBond Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group)
    (meaning : Log.PhysicalSU2PrincipalLogMeaning
      Field CoarseBond FineBond
      (R126.Vector (R146.additive C)) Group Radius) →
  CMP98RelativeContourPhysicalBridge source meaning →
  R154.UniformLeftRightDexpFamily (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
physicalPrincipalImageOneStepDerivative source meaning bridge calculus =
  R156.existingPrincipalLogOneStepDerivative
    source (Log.chart meaning) calculus

physicalPrincipalImageMultiscaleDerivative :
  ∀ {C n Group group Field CoarseBond FineBond Radius}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Group group)
    (meaning : Log.PhysicalSU2PrincipalLogMeaning
      Field CoarseBond FineBond
      (R126.Vector (R146.additive C)) Group Radius) →
  CMP98RelativeContourPhysicalBridge source meaning →
  R154.UniformLeftRightDexpFamily (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
physicalPrincipalImageMultiscaleDerivative source meaning bridge calculus =
  R156.existingPrincipalLogMultiscaleDerivative
    source (Log.chart meaning) calculus

cmp98Equation119PhysicalPrincipalImageRound157Level : ProofLevel
cmp98Equation119PhysicalPrincipalImageRound157Level = machineChecked

cmp98Equation119PhysicalLogSamePointYRound157Level : ProofLevel
cmp98Equation119PhysicalLogSamePointYRound157Level = machineChecked

-- The fresh per-point image receipt has disappeared.  Remaining physical seams:
--   (1) identify Round155's literal relative contour with the existing physical
--       transported-relative object on the same source background;
--   (2) identify that physical log normalization with CMP98's printed (1/i)log;
--   (3) instantiate one uniform LR/dexp family at the resulting Y values.
-- Radius/image admission itself is downstream from PhysicalSmallField.
literalCMP98RelativeContourSameObjectRound157Level : ProofLevel
literalCMP98RelativeContourSameObjectRound157Level = conditional

literalCMP98PhysicalLogOverINormalizationRound157Level : ProofLevel
literalCMP98PhysicalLogOverINormalizationRound157Level = conditional

literalCMP98UniformDexpAtPhysicalLogRound157Level : ProofLevel
literalCMP98UniformDexpAtPhysicalLogRound157Level = conditional
