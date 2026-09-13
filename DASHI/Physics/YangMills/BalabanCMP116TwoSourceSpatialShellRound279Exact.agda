{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116TwoSourceSpatialShellRound279Exact where

------------------------------------------------------------------------
-- ROUND279 / TWO-SOURCE LOG RESPONSE -> EXISTING CMP116 SPATIAL SHELL
--
-- `NormalizedTwoSourceConnectedCumulantExact` removes the algebraic gap:
-- the mixed log-J derivative is the connected covariance once the literal J
-- directions are identified.  CMP116 differentiated localization says finite
-- source derivatives preserve the external rooted/tree exponential majorant.
--
-- The physical-spatial grade is the EXISTING `hessianMark`; derivative order is
-- not a new distance coordinate.  This owner compiles one literal shell
-- identification into the explicit geometric covariance bound.  No Heat/Doob,
-- Langevin, Dyson, or new clustering architecture is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant

record CMP116TwoSourceSpatialShell
    (Scale Volume Root Observable : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root

    rootOfPair : Observable → Observable → Root
    physicalDistance : Observable → Observable → Nat

    twoSourceConnectedShell : Scale → Volume → Root → Nat → ℚ
    connectedCovarianceMagnitude :
      Scale → Volume → Observable → Observable → ℚ

    -- SAME-OBJECT source semantics: the selected pair covariance is literally
    -- the mixed log-J response organized by its connecting rooted shell.
    covarianceIsTwoSourceShell : ∀ scale volume left right →
      connectedCovarianceMagnitude scale volume left right
      ≡ twoSourceConnectedShell scale volume (rootOfPair left right)
          (physicalDistance left right)

    -- The one surviving analytic/source theorem.  CMP116's Cauchy-differentiated
    -- localization must be instantiated with the literal two J directions on
    -- the common physical-spatial grade.
    twoSourceShellBelowHessianMarkedAnalytic :
      ∀ scale volume root depth →
      twoSourceConnectedShell scale volume root depth
      ≤ Shared.markedAnalyticShell shared Shared.hessianMark
          scale volume root depth

open CMP116TwoSourceSpatialShell public

connectedCovarianceBelowRootedShell :
  ∀ {Scale Volume Root Observable}
    (dataSet : CMP116TwoSourceSpatialShell Scale Volume Root Observable)
    scale volume left right →
  connectedCovarianceMagnitude dataSet scale volume left right
  ≤ Shared.hessianAnalyticConstant (shared dataSet)
      * StepV.rootedShell
          (Shared.kpShell (shared dataSet) Shared.hessianMark)
          scale volume (rootOfPair dataSet left right)
          (physicalDistance dataSet left right)
connectedCovarianceBelowRootedShell dataSet scale volume left right =
  subst
    (λ lower → lower
      ≤ Shared.hessianAnalyticConstant (shared dataSet)
          * StepV.rootedShell
              (Shared.kpShell (shared dataSet) Shared.hessianMark)
              scale volume (rootOfPair dataSet left right)
              (physicalDistance dataSet left right))
    (sym (covarianceIsTwoSourceShell dataSet scale volume left right))
    (ℚP.≤-trans
      (twoSourceShellBelowHessianMarkedAnalytic dataSet
        scale volume (rootOfPair dataSet left right)
        (physicalDistance dataSet left right))
      (Shared.markedAnalyticShellBelowRooted
        (shared dataSet) Shared.hessianMark
        scale volume (rootOfPair dataSet left right)
        (physicalDistance dataSet left right)))

connectedCovarianceGeometricBound :
  ∀ {Scale Volume Root Observable}
    (dataSet : CMP116TwoSourceSpatialShell Scale Volume Root Observable)
    scale volume left right →
  connectedCovarianceMagnitude dataSet scale volume left right
  ≤ Shared.hessianAnalyticConstant (shared dataSet)
      * (StepV.quarter * Geo.halfPower (physicalDistance dataSet left right))
connectedCovarianceGeometricBound dataSet scale volume left right =
  let
    first = connectedCovarianceBelowRootedShell
      dataSet scale volume left right
    rooted = StepV.rootedShellBelowMajorant
      (Shared.kpShell (shared dataSet) Shared.hessianMark)
      scale volume (rootOfPair dataSet left right)
      (physicalDistance dataSet left right)
    scaled = Norm.scaleNonnegative
      (Shared.hessianAnalyticConstant (shared dataSet))
      (Shared.markedConstantNonnegative (shared dataSet) Shared.hessianMark)
      rooted
  in
  ℚP.≤-trans first scaled

round279TwoSourceSpatialShellCompilerLevel : ProofLevel
round279TwoSourceSpatialShellCompilerLevel = machineChecked

round279NormalizedTwoSourceCumulantLevel : ProofLevel
round279NormalizedTwoSourceCumulantLevel = Cumulant.twoSourceConnectedCumulantCompilerLevel

round279CMP116DifferentiatedLocalizationLevel : ProofLevel
round279CMP116DifferentiatedLocalizationLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

-- This is now the exact wall on the source-native route: instantiate CMP116's
-- differentiated localization with TWO literal physical J insertions and the
-- mixed log-generating-functional response, on the same hessian/spatial shell.
-- Everything after this field in R279 is compiler-owned.
round279LiteralTwoJDirectionsToSpatialShellLevel : ProofLevel
round279LiteralTwoJDirectionsToSpatialShellLevel = conditional
