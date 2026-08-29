{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact where

------------------------------------------------------------------------
-- ROW B: SHARED CMP116 MARKED CONTROL ALREADY IMPLIES GEOMETRIC SHELL DECAY
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared

mulNN : ∀ {left right} → 0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
mulNN {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = ℚ.nonNegative leftNN
      rightNonnegative : NonNegative right
      rightNonnegative = ℚ.nonNegative rightNN
  in
  ℚP.nonNegative⁻¹ (left * right)

quarterNN : 0ℚ ≤ StepV.quarter
quarterNN = toWitness {a? = 0ℚ ℚP.≤? StepV.quarter} _

markedBaseEnergy :
  ∀ {Scale Volume Root} →
  Shared.SharedMarkedAnalyticShellControl Scale Volume Root →
  Shared.MarkedResponseKind → ℚ
markedBaseEnergy dataSet kind =
  StepV.quarter * Shared.markedConstant dataSet kind

markedBaseEnergyNonnegative :
  ∀ {Scale Volume Root}
    (dataSet : Shared.SharedMarkedAnalyticShellControl Scale Volume Root)
    kind →
  0ℚ ≤ markedBaseEnergy dataSet kind
markedBaseEnergyNonnegative dataSet kind =
  mulNN quarterNN (Shared.markedConstantNonnegative dataSet kind)

markedAnalyticShellGeometricHalf :
  ∀ {Scale Volume Root}
    (dataSet : Shared.SharedMarkedAnalyticShellControl Scale Volume Root)
    kind scale volume root depth →
  Shared.markedAnalyticShell dataSet kind scale volume root depth
  ≤ markedBaseEnergy dataSet kind * Geo.halfPower depth
markedAnalyticShellGeometricHalf dataSet kind scale volume root depth =
  let
    first = Shared.markedAnalyticShellBelowRooted
      dataSet kind scale volume root depth
    rooted = StepV.rootedShellBelowMajorant
      (Shared.kpShell dataSet kind) scale volume root depth
    scaled = Norm.scaleNonnegative
      (Shared.markedConstant dataSet kind)
      (Shared.markedConstantNonnegative dataSet kind)
      rooted
  in
  ℚP.≤-trans first
    (subst
      (λ upper →
        Shared.markedConstant dataSet kind
          * StepV.rootedShell (Shared.kpShell dataSet kind)
              scale volume root depth
        ≤ upper)
      (ℚRing.solve-∀
        (Shared.markedConstant dataSet kind)
        StepV.quarter
        (Geo.halfPower depth))
      scaled)

responseGeometricHalf :
  ∀ {Scale Volume Root}
    (dataSet : Shared.SharedMarkedAnalyticShellControl Scale Volume Root)
    (kind : Shared.MarkedResponseKind)
    (response : Scale → Volume → Root → Nat → ℚ) →
    (∀ scale volume root depth →
      response scale volume root depth
      ≤ Shared.markedAnalyticShell dataSet kind scale volume root depth) →
    ∀ scale volume root depth →
  response scale volume root depth
  ≤ markedBaseEnergy dataSet kind * Geo.halfPower depth
responseGeometricHalf dataSet kind response responseBelow scale volume root depth =
  ℚP.≤-trans
    (responseBelow scale volume root depth)
    (markedAnalyticShellGeometricHalf
      dataSet kind scale volume root depth)

betaHistoryGeometricHalf :
  ∀ {Scale Volume Root}
    (dataSet : Shared.SharedMarkedAnalyticShellControl Scale Volume Root)
    scale volume root depth →
  Shared.betaHistoryShell dataSet scale volume root depth
  ≤ markedBaseEnergy dataSet Shared.betaMark * Geo.halfPower depth
betaHistoryGeometricHalf dataSet =
  responseGeometricHalf dataSet Shared.betaMark
    (Shared.betaHistoryShell dataSet)
    (Shared.betaBelowAnalytic dataSet)

hessianInfluenceGeometricHalf :
  ∀ {Scale Volume Root}
    (dataSet : Shared.SharedMarkedAnalyticShellControl Scale Volume Root)
    scale volume root depth →
  Shared.hessianInfluenceShell dataSet scale volume root depth
  ≤ markedBaseEnergy dataSet Shared.hessianMark * Geo.halfPower depth
hessianInfluenceGeometricHalf dataSet =
  responseGeometricHalf dataSet Shared.hessianMark
    (Shared.hessianInfluenceShell dataSet)
    (Shared.hessianBelowAnalytic dataSet)

compositeInsertionGeometricHalf :
  ∀ {Scale Volume Root}
    (dataSet : Shared.SharedMarkedAnalyticShellControl Scale Volume Root)
    scale volume root depth →
  Shared.compositeInsertionShell dataSet scale volume root depth
  ≤ markedBaseEnergy dataSet Shared.compositeMark * Geo.halfPower depth
compositeInsertionGeometricHalf dataSet =
  responseGeometricHalf dataSet Shared.compositeMark
    (Shared.compositeInsertionShell dataSet)
    (Shared.compositeBelowAnalytic dataSet)

record StressBelowCompositeMarkedShell
    {Scale Volume Root : Set}
    (dataSet : Shared.SharedMarkedAnalyticShellControl Scale Volume Root) : Set₁ where
  field
    stressShell : Scale → Volume → Root → Nat → ℚ
    stressBelowComposite : ∀ scale volume root depth →
      stressShell scale volume root depth
      ≤ Shared.compositeInsertionShell dataSet scale volume root depth

open StressBelowCompositeMarkedShell public

stressGeometricHalf :
  ∀ {Scale Volume Root}
    {dataSet : Shared.SharedMarkedAnalyticShellControl Scale Volume Root}
    (stress : StressBelowCompositeMarkedShell dataSet)
    scale volume root depth →
  stressShell stress scale volume root depth
  ≤ markedBaseEnergy dataSet Shared.compositeMark * Geo.halfPower depth
stressGeometricHalf {dataSet = dataSet} stress scale volume root depth =
  ℚP.≤-trans
    (stressBelowComposite stress scale volume root depth)
    (compositeInsertionGeometricHalf dataSet scale volume root depth)

sharedMarkedControlToGeometricHalfLevel : ProofLevel
sharedMarkedControlToGeometricHalfLevel = machineChecked

sharedHessianGeometricShellLevel : ProofLevel
sharedHessianGeometricShellLevel = machineChecked

sharedCompositeGeometricShellLevel : ProofLevel
sharedCompositeGeometricShellLevel = machineChecked

stressBelowCompositeToGeometricShellLevel : ProofLevel
stressBelowCompositeToGeometricShellLevel = machineChecked

physicalCMP116SharedMarkedControlInstantiationLevel : ProofLevel
physicalCMP116SharedMarkedControlInstantiationLevel = conditional

physicalStressToCompositeMarkedShellIdentificationLevel : ProofLevel
physicalStressToCompositeMarkedShellIdentificationLevel = conditional
