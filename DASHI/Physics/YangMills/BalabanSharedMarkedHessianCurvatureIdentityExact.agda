{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSharedMarkedHessianCurvatureIdentityExact where

------------------------------------------------------------------------
-- ROW C TEMPORAL: SAME-OBJECT HEAT/DOOB CURVATURE SHELL -> CMP116 HESSIAN MARK
--
-- The existing B->C temporal adapter asks for
--
--       eta_n <= H_n,
--
-- where H_n is the literal CMP116 hessian mark.  In the intended same-density
-- Heat/Doob construction the strongest/highest-alpha route is to identify eta_n
-- directly with the negative Hessian shell already measured by that mark.  Then
-- the comparison is reflexive and all 17/32 summation is downstream.
--
-- This file makes that source-identification route explicit.  It does NOT claim
-- the identity physically; it proves that once the literal shell equality is
-- supplied, no separate temporal inequality remains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianToCurvatureDebtExact as Curv
import DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact as Debt
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact as Tail
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geom

record LiteralCurvatureHessianShellIdentification
    (Scale Volume Root : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    curvatureDebt : Nat → ℚ
    curvatureDebtNonnegative : ∀ n → 0ℚ ≤ curvatureDebt n

    -- Literal same-density source identity.  If the Heat/Doob negative Hessian
    -- debt is represented by the same differentiated shell, no second numerical
    -- comparison is needed.
    curvatureDebtIsPhysicalHessianShell : ∀ n →
      curvatureDebt n
      ≡ Shared.hessianInfluenceShell shared scale volume root n

open LiteralCurvatureHessianShellIdentification public

curvatureBelowPhysicalHessian :
  ∀ {Scale Volume Root}
    (dataSet : LiteralCurvatureHessianShellIdentification Scale Volume Root)
    n →
  curvatureDebt dataSet n
  ≤ Shared.hessianInfluenceShell
      (shared dataSet) (scale dataSet) (volume dataSet) (root dataSet) n
curvatureBelowPhysicalHessian dataSet n =
  subst
    (λ left → left ≤
      Shared.hessianInfluenceShell
        (shared dataSet) (scale dataSet) (volume dataSet) (root dataSet) n)
    (curvatureDebtIsPhysicalHessianShell dataSet n)
    ℚP.≤-refl

asSharedHessianCurvatureDomination :
  ∀ {Scale Volume Root} →
  LiteralCurvatureHessianShellIdentification Scale Volume Root →
  Curv.SharedHessianCurvatureDomination Scale Volume Root
asSharedHessianCurvatureDomination dataSet = record
  { Curv.SharedHessianCurvatureDomination.shared = shared dataSet
  ; Curv.SharedHessianCurvatureDomination.scale = scale dataSet
  ; Curv.SharedHessianCurvatureDomination.volume = volume dataSet
  ; Curv.SharedHessianCurvatureDomination.root = root dataSet
  ; Curv.SharedHessianCurvatureDomination.curvatureDebt = curvatureDebt dataSet
  ; Curv.SharedHessianCurvatureDomination.curvatureDebtNonnegative =
      curvatureDebtNonnegative dataSet
  ; Curv.SharedHessianCurvatureDomination.curvatureBelowPhysicalHessianMark =
      curvatureBelowPhysicalHessian dataSet
  }

sameObjectCurvatureUniformDebt :
  ∀ {Scale Volume Root}
    (dataSet : LiteralCurvatureHessianShellIdentification Scale Volume Root)
    count →
  Debt.finiteCurvatureDebt
    (Curv.asGeometricNegativeCurvatureDebt
      (asSharedHessianCurvatureDomination dataSet)) count
  ≤ Tail.tailFactor
      * Geom.markedBaseEnergy (shared dataSet) Shared.hessianMark
sameObjectCurvatureUniformDebt dataSet =
  Curv.sharedHessianPaysUniformCurvatureDebt
    (asSharedHessianCurvatureDomination dataSet)

sameObjectCurvatureToHessianDominationLevel : ProofLevel
sameObjectCurvatureToHessianDominationLevel = machineChecked

sameObjectCurvatureToUniformDebtLevel : ProofLevel
sameObjectCurvatureToUniformDebtLevel = machineChecked

-- Preferred temporal source seam: identify the negative same-density Heat/Doob
-- curvature shell with the literal CMP116 physical Hessian shell.  If the source
-- construction yields only domination rather than equality, the older adapter
-- remains available and is logically weaker.
literalHeatDoobCurvatureIsCMP116HessianShellLevel : ProofLevel
literalHeatDoobCurvatureIsCMP116HessianShellLevel = conditional
