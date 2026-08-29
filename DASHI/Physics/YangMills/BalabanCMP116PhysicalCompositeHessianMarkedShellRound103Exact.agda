{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PhysicalCompositeHessianMarkedShellRound103Exact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geom
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius

record PhysicalCompositeHessianMarkedShell
    (Scale Volume Root : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    radiusData : Radius.CMP116CommonAnalyticRadius Scale Volume

    physicalCompositeHessianShell :
      Scale → Volume → Root → Nat → ℚ
    physicalCompositeHessianShellNonnegative :
      ∀ scale volume root depth →
      0ℚ ≤ physicalCompositeHessianShell scale volume root depth

    physicalShellIsSharedHessianShell : ∀ scale volume root depth →
      physicalCompositeHessianShell scale volume root depth
      ≡ Shared.hessianInfluenceShell shared scale volume root depth

    physicalHessianUsesCommonRadius : Scale → Volume → Set

open PhysicalCompositeHessianMarkedShell public

physicalCompositeHessianBelowMarkedAnalytic :
  ∀ {Scale Volume Root}
    (dataSet : PhysicalCompositeHessianMarkedShell Scale Volume Root)
    scale volume root depth →
  physicalCompositeHessianShell dataSet scale volume root depth
  ≤ Shared.markedAnalyticShell
      (shared dataSet) Shared.hessianMark scale volume root depth
physicalCompositeHessianBelowMarkedAnalytic dataSet scale volume root depth
  rewrite physicalShellIsSharedHessianShell dataSet scale volume root depth =
  Shared.hessianBelowAnalytic (shared dataSet) scale volume root depth

physicalCompositeHessianGeometricHalf :
  ∀ {Scale Volume Root}
    (dataSet : PhysicalCompositeHessianMarkedShell Scale Volume Root)
    scale volume root depth →
  physicalCompositeHessianShell dataSet scale volume root depth
  ≤ Geom.markedBaseEnergy (shared dataSet) Shared.hessianMark
      * Geo.halfPower depth
physicalCompositeHessianGeometricHalf dataSet scale volume root depth =
  Geom.responseGeometricHalf
    (shared dataSet) Shared.hessianMark
    (physicalCompositeHessianShell dataSet)
    (physicalCompositeHessianBelowMarkedAnalytic dataSet)
    scale volume root depth

physicalCompositeHessianMarkedShellCompilerLevel : ProofLevel
physicalCompositeHessianMarkedShellCompilerLevel = machineChecked

literalCMP116PhysicalCompositeHessianShellIdentificationLevel : ProofLevel
literalCMP116PhysicalCompositeHessianShellIdentificationLevel = conditional
