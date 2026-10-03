{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressObservableHingeExact where

------------------------------------------------------------------------
-- ONE STRESS -> OBSERVABLE HINGE FOR BOTH MARKED E2 AND MARKED E4.
--
-- R403 already removes a separate observable -> J/source-direction debt on the
-- selected T5/R274 route: the observable itself can be the source direction.
-- Therefore E2 and E4 should not be allowed to choose different observable
-- realizations of the stress mark.
--
-- This owner fixes ONE encoding
--
--   encodeStress : StressMark -> Observable
--
-- and reuses it for:
--   * E2 inclusion in the reflected positive-time cylinder algebra;
--   * E4 selection of the stress observable in the R274 clustering theorem.
--
-- The remaining obligations are semantic/admissibility laws on that one map,
-- not two independent same-object selections.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE2CylinderEmbeddingExact as E2
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE4ClusteringExact as E4
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274

record SharedStressObservableHinge
    {Scale Volume Root State Observable StressMark : Set}
    (observableAlgebra : OS2.CylinderOSAlgebra Observable)
    (twoSource :
      R274.TwoSourceConnectedRootedShellData
        Scale Volume Root State Observable)
    : Set₁ where
  field
    encodeStress : StressMark → Observable
    selectedStressMark : StressMark

open SharedStressObservableHinge public

selectedStressObservable :
  ∀ {Scale Volume Root State Observable StressMark observableAlgebra twoSource} →
  SharedStressObservableHinge
    {Scale = Scale} {Volume = Volume} {Root = Root}
    {State = State} {Observable = Observable} {StressMark = StressMark}
    observableAlgebra twoSource →
  Observable
selectedStressObservable hinge =
  encodeStress hinge (selectedStressMark hinge)

record SharedStressE2Admissibility
    {Scale Volume Root State Observable StressMark : Set}
    {observableAlgebra : OS2.CylinderOSAlgebra Observable}
    {twoSource :
      R274.TwoSourceConnectedRootedShellData
        Scale Volume Root State Observable}
    (hinge :
      SharedStressObservableHinge observableAlgebra twoSource)
    : Set₁ where
  field
    PositiveTimeSupported : Observable → Set
    GaugeInvariantObservable : Observable → Set

    stressPositiveTime : ∀ mark →
      PositiveTimeSupported (encodeStress hinge mark)

    stressGaugeInvariant : ∀ mark →
      GaugeInvariantObservable (encodeStress hinge mark)

    reflectStressMark : StressMark → StressMark

    encodeCommutesWithReflection : ∀ mark →
      encodeStress hinge (reflectStressMark mark)
      ≡ OS2.reflectObservable observableAlgebra (encodeStress hinge mark)

open SharedStressE2Admissibility public

asMarkedE2CylinderEmbedding :
  ∀ {Scale Volume Root State Observable StressMark observableAlgebra twoSource}
    {hinge :
      SharedStressObservableHinge
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {State = State} {Observable = Observable} {StressMark = StressMark}
        observableAlgebra twoSource} →
  SharedStressE2Admissibility hinge →
  E2.MarkedStressCylinderEmbedding
    Observable StressMark observableAlgebra
asMarkedE2CylinderEmbedding {hinge = hinge} dataSet = record
  { E2.MarkedStressCylinderEmbedding.encodeStress = encodeStress hinge
  ; E2.MarkedStressCylinderEmbedding.PositiveTimeSupported =
      PositiveTimeSupported dataSet
  ; E2.MarkedStressCylinderEmbedding.GaugeInvariantObservable =
      GaugeInvariantObservable dataSet
  ; E2.MarkedStressCylinderEmbedding.stressPositiveTime =
      stressPositiveTime dataSet
  ; E2.MarkedStressCylinderEmbedding.stressGaugeInvariant =
      stressGaugeInvariant dataSet
  ; E2.MarkedStressCylinderEmbedding.reflectStressMark =
      reflectStressMark dataSet
  ; E2.MarkedStressCylinderEmbedding.encodeCommutesWithReflection =
      encodeCommutesWithReflection dataSet
  }

record SharedStressE4Semantics
    {Scale Volume Root State Observable StressMark : Set}
    {observableAlgebra : OS2.CylinderOSAlgebra Observable}
    {twoSource :
      R274.TwoSourceConnectedRootedShellData
        Scale Volume Root State Observable}
    (hinge : SharedStressObservableHinge observableAlgebra twoSource)
    : Set₁ where
  field
    MarkedE4ClusterCompatibility : Set

    quantitativeStressClusteringImpliesMarkedE4 :
      (∀ state other →
        R274.connectedCovarianceMagnitude twoSource
          state (selectedStressObservable hinge) other
        ≤
        DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact.quarter
        *
        DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact.rationalPower
          DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact.half
          (R274.physicalDistance twoSource
            (selectedStressObservable hinge) other))
      → MarkedE4ClusterCompatibility

open SharedStressE4Semantics public

asMarkedE4ClusteringAdapter :
  ∀ {Scale Volume Root State Observable StressMark observableAlgebra twoSource}
    {hinge :
      SharedStressObservableHinge
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {State = State} {Observable = Observable} {StressMark = StressMark}
        observableAlgebra twoSource} →
  SharedStressE4Semantics hinge →
  E4.MarkedStressE4ClusteringAdapter twoSource
asMarkedE4ClusteringAdapter {hinge = hinge} dataSet = record
  { E4.MarkedStressE4ClusteringAdapter.selectedStressObservable =
      selectedStressObservable hinge
  ; E4.MarkedStressE4ClusteringAdapter.MarkedE4ClusterCompatibility =
      MarkedE4ClusterCompatibility dataSet
  ; E4.MarkedStressE4ClusteringAdapter.quantitativeStressClusteringImpliesMarkedE4 =
      quantitativeStressClusteringImpliesMarkedE4 dataSet
  }

sameObservableFeedsE2AndE4 : Bool
sameObservableFeedsE2AndE4 = true

independentE2E4StressSelectionsEliminated : Bool
independentE2E4StressSelectionsEliminated = true
