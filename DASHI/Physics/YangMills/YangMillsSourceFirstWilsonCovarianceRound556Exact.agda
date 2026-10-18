{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact where

------------------------------------------------------------------------
-- GOAL-1 B / ROUND556:
-- BUILD MODERN WEXT ON THE EXACT CMP119/T5 COVARIANCE CARRIER
--
-- R551 previously accepted an abstract finite connected covariance and then
-- separately asked that this SAME Wilson correlation converge to the continuum.
--
-- R278 already proves that convergence once the finite covariance is literally
-- the selected T5/CMP119 covariance and the Wilson left/right/product tests are
-- bounded.
--
-- So choose the WEXT covariance by construction:
--
--   finiteCov_k(W_L,W_R)
--     := R278.connectedCovarianceMagnitude extension measure_k W_L W_R.
--
-- Then same-family continuum covariance convergence is compiler-owned.  The
-- physical Wilson bill remains:
--
--   * WEXT shell bound on that exact covariance;
--   * left/right/product bounded-test admissibility;
--   * Euclidean time = support distance;
--   * upper-order closure of the selected scalar convergence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanWilsonTwoInsertionConnectedShellRound491Exact as WEXT
import DASHI.Physics.YangMills.YangMillsWilsonContinuumClusteringRound551Exact as R551

record IndexedSourceFirstWilsonCovarianceData
    {Measure Observable Scale Volume Root : Set}
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (extension :
      R278.ScalarCovarianceConvergenceExtension dataSet)
    : Set₁ where
  field
    shellData : Shell.TraversalShellData Scale Volume Root

    scaleOfCutoff : Nat → Scale
    volumeOfCutoff : Nat → Volume

    physicalDistance : Observable → Observable → Nat
    connectingRoot : Nat → Observable → Observable → Root
    timeTranslate : Observable → Nat → Observable

    finiteWilsonCovarianceBelowConnectingShell :
      ∀ cutoff left right →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        left right
      ≤
      Shell.rootedShell shellData
        (scaleOfCutoff cutoff)
        (volumeOfCutoff cutoff)
        (connectingRoot cutoff left right)
        (physicalDistance left right)

    ConnectingClusterMeetsBothWilsonSupports :
      Nat → Observable → Observable → Set

    leftBounded :
      ∀ observable →
      Gram.BoundedObservable dataSet observable

    translatedRightBounded :
      ∀ observable time →
      Gram.BoundedObservable dataSet (timeTranslate observable time)

    translatedProductBounded :
      ∀ left right time →
      Gram.BoundedObservable dataSet
        (Gram.multiplyObservable (Gram.operations dataSet)
          left (timeTranslate right time))

    supportDistanceIsEuclideanTime :
      ∀ left right time →
      physicalDistance left (timeTranslate right time)
      ≡ time

    upperOrderClosed :
      ∀ sequence target upper →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open IndexedSourceFirstWilsonCovarianceData public

indexedAsWilsonWEXT :
  ∀ {Measure Observable Scale Volume Root dataSet extension} →
  IndexedSourceFirstWilsonCovarianceData
    {Measure = Measure} {Observable = Observable}
    {Scale = Scale} {Volume = Volume} {Root = Root}
    dataSet extension →
  WEXT.WilsonTwoInsertionConnectedShell
    Scale Volume Root Nat Observable
indexedAsWilsonWEXT {dataSet = dataSet} {extension = extension} source = record
  { WEXT.WilsonTwoInsertionConnectedShell.shellData =
      shellData source
  ; WEXT.WilsonTwoInsertionConnectedShell.stateAtScale =
      λ cutoff → cutoff
  ; WEXT.WilsonTwoInsertionConnectedShell.scaleOf =
      scaleOfCutoff source
  ; WEXT.WilsonTwoInsertionConnectedShell.volumeOf =
      volumeOfCutoff source
  ; WEXT.WilsonTwoInsertionConnectedShell.physicalDistance =
      physicalDistance source
  ; WEXT.WilsonTwoInsertionConnectedShell.connectingRoot =
      connectingRoot source
  ; WEXT.WilsonTwoInsertionConnectedShell.connectedCovarianceMagnitude =
      λ cutoff left right →
        R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence dataSet cutoff)
          left right
  ; WEXT.WilsonTwoInsertionConnectedShell.wilsonConnectedCovarianceBelowConnectingShell =
      finiteWilsonCovarianceBelowConnectingShell source
  ; WEXT.WilsonTwoInsertionConnectedShell.connectingClusterMeetsBothWilsonSupports =
      ConnectingClusterMeetsBothWilsonSupports source
  }

pairTests :
  ∀ {Measure Observable Scale Volume Root dataSet extension}
    (source :
      IndexedSourceFirstWilsonCovarianceData
        {Measure = Measure} {Observable = Observable}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        dataSet extension)
    left right time →
  R278.SelectedConnectedCovarianceTests dataSet
pairTests source left right time = record
  { R278.SelectedConnectedCovarianceTests.Index =
      ⊤
  ; R278.SelectedConnectedCovarianceTests.left =
      λ _ → left
  ; R278.SelectedConnectedCovarianceTests.right =
      λ _ → timeTranslate source right time
  ; R278.SelectedConnectedCovarianceTests.leftBounded =
      λ _ → leftBounded source left
  ; R278.SelectedConnectedCovarianceTests.rightBounded =
      λ _ → translatedRightBounded source right time
  ; R278.SelectedConnectedCovarianceTests.productBounded =
      λ _ → translatedProductBounded source left right time
  }

continuumCovariance :
  ∀ {Measure Observable Scale Volume Root dataSet extension} →
  IndexedSourceFirstWilsonCovarianceData
    {Measure = Measure} {Observable = Observable}
    {Scale = Scale} {Volume = Volume} {Root = Root}
    dataSet extension →
  Observable → Observable → Nat → ℚ
continuumCovariance {dataSet = dataSet} {extension = extension}
    source left right time =
  R278.connectedCovarianceMagnitude extension
    (Gram.continuumMeasure dataSet)
    left
    (timeTranslate source right time)

indexedAsContinuumClustering :
  ∀ {Measure Observable Scale Volume Root dataSet extension} →
  (source :
    IndexedSourceFirstWilsonCovarianceData
      {Measure = Measure} {Observable = Observable}
      {Scale = Scale} {Volume = Volume} {Root = Root}
      dataSet extension) →
  R551.WilsonContinuumClusteringInputs
    (indexedAsWilsonWEXT source)
indexedAsContinuumClustering
    {dataSet = dataSet} {extension = extension} source = record
  { R551.WilsonContinuumClusteringInputs.timeTranslate =
      timeTranslate source
  ; R551.WilsonContinuumClusteringInputs.continuumConnectedCovarianceMagnitude =
      continuumCovariance source
  ; R551.WilsonContinuumClusteringInputs.Converges =
      Gram.Converges (Gram.scalarConvergence dataSet)
  ; R551.WilsonContinuumClusteringInputs.sameFamilyWilsonCorrelationConverges =
      λ left right time →
        R278.selectedConnectedCovarianceMagnitudeConverges
          extension
          (pairTests source left right time)
          tt
  ; R551.WilsonContinuumClusteringInputs.supportDistanceIsEuclideanTime =
      supportDistanceIsEuclideanTime source
  ; R551.WilsonContinuumClusteringInputs.orderClosedUnderContinuumLimit =
      upperOrderClosed source
  }

round556SameFamilyCovarianceConvergenceCompilerLevel : ProofLevel
round556SameFamilyCovarianceConvergenceCompilerLevel =
  R278.round278ConnectedCovarianceLimitCompilerLevel

round556WEXTCarrierIsExactSelectedCovarianceLevel : ProofLevel
round556WEXTCarrierIsExactSelectedCovarianceLevel = machineChecked

separateSameFamilyWilsonCovarianceConvergenceLeafRequired : Bool
separateSameFamilyWilsonCovarianceConvergenceLeafRequired = false

printedJPresentationRequired : Bool
printedJPresentationRequired = false

-- Still physical: Wilson WEXT itself, bounded-test/source presentation,
-- Euclidean time/support meaning and order closure.
literalRound556SourceFirstWilsonCarrierLevel : ProofLevel
literalRound556SourceFirstWilsonCarrierLevel = conditional
