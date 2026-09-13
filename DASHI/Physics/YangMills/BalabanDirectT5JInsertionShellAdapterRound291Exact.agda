{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDirectT5JInsertionShellAdapterRound291Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanCMP116TwoPhysicalJInsertionNormalizationRound290Exact as R290
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact as R284
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell

record DirectT5JInsertionShellPresentation
    {Measure TestObservable : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    : Set₁ where
  field
    Scale Volume Root SourceDirection : Set
    sourcePresentation :
      R290.TwoPhysicalJInsertionSourcePresentation
        Scale Volume Root Nat TestObservable SourceDirection
    sourceCovarianceIsSelectedT5Covariance : ∀ cutoff left right →
      R290.connectedCovarianceMagnitude sourcePresentation cutoff left right
      ≡ R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence dataSet cutoff) left right
    ConnectingClusterMeetsBothSupports :
      Nat → TestObservable → TestObservable → Set

open DirectT5JInsertionShellPresentation public

selectedT5CovarianceBelowRootedShell :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (presentation : DirectT5JInsertionShellPresentation dataSet extension)
    cutoff left right →
  R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet cutoff) left right
  ≤ Shell.rootedShell
      (R290.shellData (sourcePresentation presentation))
      (R290.scaleOf (sourcePresentation presentation) cutoff)
      (R290.volumeOf (sourcePresentation presentation) cutoff)
      (R290.connectingRoot (sourcePresentation presentation) cutoff left right)
      (R290.physicalDistance (sourcePresentation presentation) left right)
selectedT5CovarianceBelowRootedShell presentation cutoff left right
  rewrite R290.symEq
    (sourceCovarianceIsSelectedT5Covariance presentation cutoff left right) =
  R290.physicalCovarianceBelowRootedShell
    (sourcePresentation presentation) cutoff left right

asDirectT5TwoSourceShell :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  DirectT5JInsertionShellPresentation dataSet extension →
  R284.DirectT5TwoSourceShell dataSet extension
asDirectT5TwoSourceShell presentation = record
  { R284.DirectT5TwoSourceShell.Scale = Scale presentation
  ; R284.DirectT5TwoSourceShell.Volume = Volume presentation
  ; R284.DirectT5TwoSourceShell.Root = Root presentation
  ; R284.DirectT5TwoSourceShell.shellData =
      R290.shellData (sourcePresentation presentation)
  ; R284.DirectT5TwoSourceShell.scaleAtCutoff =
      R290.scaleOf (sourcePresentation presentation)
  ; R284.DirectT5TwoSourceShell.volumeAtCutoff =
      R290.volumeOf (sourcePresentation presentation)
  ; R284.DirectT5TwoSourceShell.physicalDistance =
      R290.physicalDistance (sourcePresentation presentation)
  ; R284.DirectT5TwoSourceShell.connectingRoot =
      R290.connectingRoot (sourcePresentation presentation)
  ; R284.DirectT5TwoSourceShell.finiteCovarianceBelowConnectingShell =
      selectedT5CovarianceBelowRootedShell presentation
  ; R284.DirectT5TwoSourceShell.connectingClusterMeetsBothSupports =
      ConnectingClusterMeetsBothSupports presentation
  }

record Round291Boundary : Set where
  constructor round291-boundary
  field
    monolithicTwoSourceShellPrimitive : Bool
    monolithicTwoSourceShellPrimitiveIsFalse :
      monolithicTwoSourceShellPrimitive ≡ false
    physicalJCoordinatePresentationRequired : Bool
    physicalJCoordinatePresentationRequiredIsTrue :
      physicalJCoordinatePresentationRequired ≡ true
    sourceCovarianceSelectedT5SameObjectRequired : Bool
    sourceCovarianceSelectedT5SameObjectRequiredIsTrue :
      sourceCovarianceSelectedT5SameObjectRequired ≡ true

canonicalRound291Boundary : Round291Boundary
canonicalRound291Boundary =
  round291-boundary false refl true refl true refl

round291JInsertionToDirectT5ShellCompilerLevel : ProofLevel
round291JInsertionToDirectT5ShellCompilerLevel = machineChecked

round291PhysicalJCoordinatePresentationLevel : ProofLevel
round291PhysicalJCoordinatePresentationLevel = conditional

round291SourceCovarianceSelectedT5SameObjectLevel : ProofLevel
round291SourceCovarianceSelectedT5SameObjectLevel = conditional
