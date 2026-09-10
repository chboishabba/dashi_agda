{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDirectT5JInsertionShellAdapterRound288Exact where

------------------------------------------------------------------------
-- ROUND288 / R287 SOURCE PRESENTATION -> R284 DIRECT T5 SHELL
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanCMP116TwoPhysicalJInsertionNormalizationRound287Exact as R287
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
      R287.TwoPhysicalJInsertionSourcePresentation
        Scale Volume Root Nat TestObservable SourceDirection

    sourceCovarianceIsSelectedT5Covariance : ∀ cutoff left right →
      R287.connectedCovarianceMagnitude sourcePresentation cutoff left right
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
      (R287.shellData (sourcePresentation presentation))
      (R287.scaleOf (sourcePresentation presentation) cutoff)
      (R287.volumeOf (sourcePresentation presentation) cutoff)
      (R287.connectingRoot (sourcePresentation presentation) cutoff left right)
      (R287.physicalDistance (sourcePresentation presentation) left right)
selectedT5CovarianceBelowRootedShell presentation cutoff left right
  rewrite R287.symEq
    (sourceCovarianceIsSelectedT5Covariance presentation cutoff left right) =
  R287.physicalCovarianceBelowRootedShell
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
      R287.shellData (sourcePresentation presentation)
  ; R284.DirectT5TwoSourceShell.scaleAtCutoff =
      R287.scaleOf (sourcePresentation presentation)
  ; R284.DirectT5TwoSourceShell.volumeAtCutoff =
      R287.volumeOf (sourcePresentation presentation)
  ; R284.DirectT5TwoSourceShell.physicalDistance =
      R287.physicalDistance (sourcePresentation presentation)
  ; R284.DirectT5TwoSourceShell.connectingRoot =
      R287.connectingRoot (sourcePresentation presentation)
  ; R284.DirectT5TwoSourceShell.finiteCovarianceBelowConnectingShell =
      selectedT5CovarianceBelowRootedShell presentation
  ; R284.DirectT5TwoSourceShell.connectingClusterMeetsBothSupports =
      ConnectingClusterMeetsBothSupports presentation
  }

record Round288Boundary : Set where
  constructor round288-boundary
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

canonicalRound288Boundary : Round288Boundary
canonicalRound288Boundary =
  round288-boundary false refl true refl true refl

round288JInsertionToDirectT5ShellCompilerLevel : ProofLevel
round288JInsertionToDirectT5ShellCompilerLevel = machineChecked

round288PhysicalJCoordinatePresentationLevel : ProofLevel
round288PhysicalJCoordinatePresentationLevel = conditional

round288SourceCovarianceSelectedT5SameObjectLevel : ProofLevel
round288SourceCovarianceSelectedT5SameObjectLevel = conditional
