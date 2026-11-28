module DASHI.Cognition.PNF.X369RecursiveHypervoxelPantsSameObjectExact where

-- Full 369 hypervoxel + original 13-stage sheaf + original pants seam
-- as views of ONE retained typed state. Existing owners, not new ontology.
-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Kernel deliberately deferred. No claim that a native neural history
-- already inhabits this packet without a source-owned admission map.
open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as H
import DASHI.Foundations.RecursiveRadixHypervoxel as Radix
import DASHI.Foundations.TernaryThirteenCentralCompletionBundleSheafExact as Sheaf
import DASHI.Foundations.TernaryThirteenPantsSheafGluingTransportExact as Pants13
import DASHI.Foundations.TernaryThirteenOriginalPantsFrontierBridgeExact as Bridge13
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as Tower
import DASHI.Biology.SelfIndexedParetoHyperfabricTetrationExact as Pareto
import DASHI.Core.FactorisationSpineCrosswalkExact as Factorisation
import DASHI.Cognition.PNF.X369NativeNineStageThirteenChartExact as StageChart
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future
open import Agda.Builtin.List using (List)
import DASHI.Reasoning.TypedHyperfabricPantsNonvacuousSeamQuotientExact as Seam
import DASHI.Reasoning.TypedHyperfabricPantsSignatureCompletenessExact as Match
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Topology.TernaryPantsFrontierExact as Frontier

-- The full native H369 is not 13 trits. A depth-13 completed source
-- valuation is a separate, retained, sourced fibre above H369.
module SameSourcePacket (Residual Index : Set) where

  record Packet : Set where
    constructor packet
    field
      nativeFabric : H.TernaryHyperformalPoint
      sourceCentral : Rel.SourceCentralCompletionCarrier
      retainedResidual : Residual
      sourceIndex : Index
  open Packet public

  pack :
    H.TernaryHyperformalPoint →
    Rel.SourceCentralCompletionCarrier →
    Residual → Index → Packet
  pack = packet

  sourceParts :
    Packet →
    (H.TernaryHyperformalPoint ×
      Rel.SourceCentralCompletionCarrier) × (Residual × Index)
  sourceParts p =
    (nativeFabric p , sourceCentral p) ,
    (retainedResidual p , sourceIndex p)

  reopen :
    (H.TernaryHyperformalPoint ×
      Rel.SourceCentralCompletionCarrier) × (Residual × Index)
    → Packet
  reopen ((h , central) , (r , k)) = packet h central r k

  reopenExact : (p : Packet) → reopen (sourceParts p) ≡ p
  reopenExact (packet h central r k) = refl

  splitExact :
    (h : H.TernaryHyperformalPoint)
    (central : Rel.SourceCentralCompletionCarrier)
    (r : Residual) (k : Index) →
    sourceParts (pack h central r k) ≡ ((h , central) , (r , k))
  splitExact h central r k = refl

  -- The ACTUAL existing Stage-13 sheaf view, not a new 13th axis
  -- invented by adding to the nine-trit spatial lattice.
  originalLocalFamily : Packet → Sheaf.CentralLocalFamily
  originalLocalFamily p =
    Sheaf.restrictCentral (sourceCentral p)

  localCompatibility : (p : Packet) →
    Sheaf.centralFamilyCompatible (originalLocalFamily p)
  localCompatibility p =
    Sheaf.centralRestrictsCompatible (sourceCentral p)

  actualPants13 : Packet → Frontier.PantsPath 13
  actualPants13 p =
    Pants13.glueCompatibleLocalsToPants
      (originalLocalFamily p) (localCompatibility p)

  everyLocalReopens : (p : Packet)
    (axis : Atlas.StageAtlasZeroToEleven) →
    Sheaf.restrictCentral
      (Bridge13.pants13ToSourceCentral (actualPants13 p)) axis
    ≡ originalLocalFamily p axis
  everyLocalReopens p axis =
    Pants13.originalPantsGlueRestricts
      (originalLocalFamily p) (localCompatibility p) axis

  -- Coordinate factorization is source-relative. We retain the whole
  -- parent and only identify matched boundary SIGNATURES, not worlds.
  module SelectedSeam
    (left right : Packet → Pants.BranchChannel)
    (p : Packet)
    (interfaceEquality :
      Seam.boundarySignature (left p) ≡
      Seam.boundarySignature (right p)) where

    licensedPantsInterface :
      Pants.InterfaceMatch (left p) (right p)
    licensedPantsInterface =
      Match.signatureMatchComplete interfaceEquality

    selectedSignature : Seam.SeamSignature
    selectedSignature = Seam.boundarySignature (left p)

    rightSignatureSame :
      selectedSignature ≡ Seam.boundarySignature (right p)
    rightSignatureSame = interfaceEquality

    -- Both projections of the SAME original packet remain available.
    -- Unlike an illicit quotient this never erases the original source.
    parentReopens : reopen (sourceParts p) ≡ p
    parentReopens = reopenExact p

    source13LocalViewUnchanged :
      (axis : Atlas.StageAtlasZeroToEleven) →
      Sheaf.restrictCentral
        (Bridge13.pants13ToSourceCentral (actualPants13 p)) axis
      ≡ originalLocalFamily p axis
    source13LocalViewUnchanged = everyLocalReopens p

-- Reverse-solve the genuine source admission, rather than requesting
-- separate unrelated source→13 and source→pants mappings. ONE source
-- packet interpretation supplies BOTH original geometric projections.
module OriginalSourceAdmission
  (Residual Index Actual : Set)
  (sourceEncode : Actual →
    SameSourcePacket.Packet Residual Index)
  (sourceDecode :
    SameSourcePacket.Packet Residual Index → Actual)
  (sourceReopens : (x : Actual) →
    sourceDecode (sourceEncode x) ≡ x) where

  module P = SameSourcePacket Residual Index

  sourceHyperfabric : Actual → H.TernaryHyperformalPoint
  sourceHyperfabric x = P.nativeFabric (sourceEncode x)

  sourceLocalFamily : Actual → Sheaf.CentralLocalFamily
  sourceLocalFamily x = P.originalLocalFamily (sourceEncode x)

  sourcePants13 : Actual → Frontier.PantsPath 13
  sourcePants13 x = P.actualPants13 (sourceEncode x)

  sourceLocalCompatibility : (x : Actual) →
    Sheaf.centralFamilyCompatible (sourceLocalFamily x)
  sourceLocalCompatibility x =
    P.localCompatibility (sourceEncode x)

  sameOriginalSourceRestriction : (x : Actual)
    (axis : Atlas.StageAtlasZeroToEleven) →
    Sheaf.restrictCentral
      (Bridge13.pants13ToSourceCentral (sourcePants13 x)) axis
    ≡ sourceLocalFamily x axis
  sameOriginalSourceRestriction x axis =
    P.everyLocalReopens (sourceEncode x) axis

  originalSourceReopens : (x : Actual) →
    sourceDecode (sourceEncode x) ≡ x
  originalSourceReopens = sourceReopens

  module OriginalSeam
    (left right : Actual → Pants.BranchChannel)
    (x : Actual)
    (matched :
      Seam.boundarySignature (left x) ≡
      Seam.boundarySignature (right x)) where

    sourceInterface : Pants.InterfaceMatch (left x) (right x)
    sourceInterface = Match.signatureMatchComplete matched

    sourcePants13PreservesLocal : (axis : Atlas.StageAtlasZeroToEleven) →
      Sheaf.restrictCentral
        (Bridge13.pants13ToSourceCentral (sourcePants13 x)) axis
      ≡ sourceLocalFamily x axis
    sourcePants13PreservesLocal = sameOriginalSourceRestriction x

    sourceHistoryRetained : sourceDecode (sourceEncode x) ≡ x
    sourceHistoryRetained = sourceReopens x

  -- Only the original source commuting squares remain to transport
  -- ALL subsequent consumer observations. The selected chart can
  -- retain any native9/stage13/pants signature/fine residual/index mix.
  -- This is a specialization of the pre-existing future theorem,
  -- not a new factorisation calculus.
  module OriginalFuture {Input Code Output : Set}
    (sourceStep : Input → Actual → Actual)
    (sourceObserve : Input → Actual → Output)
    (select : P.Packet → Code)
    (codedStep : Input → Code → Code)
    (codedObserve : Input → Code → Output)
    (transitionSquare : (u : Input) (x : Actual) →
      select (sourceEncode (sourceStep u x)) ≡
      codedStep u (select (sourceEncode x)))
    (observationSquare : (u : Input) (x : Actual) →
      sourceObserve u x ≡
      codedObserve u (select (sourceEncode x))) where

    chart : Actual → Code
    chart x = select (sourceEncode x)

    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl

    trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    trans refl q = q

    consumerStable : (u : Input) (x y : Actual) →
      chart x ≡ chart y →
      sourceObserve u x ≡ sourceObserve u y
    consumerStable u x y same =
      trans (observationSquare u x)
        (trans (Future.cong (codedObserve u) same)
          (sym (observationSquare u y)))

    transitionStable : (u : Input) (x y : Actual) →
      chart x ≡ chart y →
      chart (sourceStep u x) ≡ chart (sourceStep u y)
    transitionStable u x y same =
      trans (transitionSquare u x)
        (trans (Future.cong (codedStep u) same)
          (sym (transitionSquare u y)))

    allOriginalFutureTraces : (words : List Input) (x y : Actual) →
      chart x ≡ chart y →
      Future.trace sourceStep sourceObserve words x ≡
      Future.trace sourceStep sourceObserve words y
    allOriginalFutureTraces words x y same =
      Future.inputIndexedTraceDescent
        sourceStep sourceObserve chart
        consumerStable transitionStable words x y same

-- Concrete CHOSEN finite instantiation of the source packet; not
-- merely a conditional source-family socket. The actual full H369
-- nine-trit address PLUS four independently retained stage trits
-- constructs an original Stage13 global source section and all pants
-- local restrictions via existing donors.
module NinePlusFourSourceSpecimen (Residual Index : Set) where
  module P = SameSourcePacket Residual Index

  nativeWithStageResidual :
    (h : H.TernaryHyperformalPoint)
    (lastFour : StageChart.StageFour) →
    Residual → Index → P.Packet
  nativeWithStageResidual h lastFour r k =
    P.packet h
      (StageChart.sourceCentralFromNinePlusFour
        (H.fabricToNineTrits h) lastFour)
      r k

  nativeNineRecovered :
    (h : H.TernaryHyperformalPoint)
    (lastFour : StageChart.StageFour)
    (r : Residual) (k : Index) →
    StageChart.nativeNineFromCentral
      (P.sourceCentral (nativeWithStageResidual h lastFour r k))
    ≡ H.fabricToNineTrits h
  nativeNineRecovered h lastFour r k =
    StageChart.nineBidi (H.fabricToNineTrits h) lastFour

  stageFourRecovered :
    (h : H.TernaryHyperformalPoint)
    (lastFour : StageChart.StageFour)
    (r : Residual) (k : Index) →
    StageChart.stageFourFromCentral
      (P.sourceCentral (nativeWithStageResidual h lastFour r k))
    ≡ lastFour
  stageFourRecovered h lastFour r k =
    StageChart.fourBidi (H.fabricToNineTrits h) lastFour

  actualThirteenPantsRestrictions :
    (h : H.TernaryHyperformalPoint)
    (lastFour : StageChart.StageFour)
    (r : Residual) (k : Index)
    (axis : Atlas.StageAtlasZeroToEleven) →
    Sheaf.restrictCentral
      (Bridge13.pants13ToSourceCentral
        (P.actualPants13 (nativeWithStageResidual h lastFour r k))) axis
    ≡
    P.originalLocalFamily
      (nativeWithStageResidual h lastFour r k) axis
  actualThirteenPantsRestrictions h lastFour r k axis =
    P.everyLocalReopens (nativeWithStageResidual h lastFour r k) axis

  fullNativeAndSourceRetained :
    (h : H.TernaryHyperformalPoint)
    (lastFour : StageChart.StageFour)
    (r : Residual) (k : Index) →
    P.reopen (P.sourceParts (nativeWithStageResidual h lastFour r k))
    ≡ nativeWithStageResidual h lastFour r k
  fullNativeAndSourceRetained h lastFour r k =
    P.reopenExact (nativeWithStageResidual h lastFour r k)

-- Actual depth-dependent radix refinement is a DIFFERENT constructor:
-- rank and depth are distinct, not a fiat equality with nine channels.
radixJoinKeepsCoarse :
  ∀ {rank depth} (coarse : Radix.TernaryAddress rank depth) →
  Radix.joinAddress coarse Radix.suffix-root ≡ coarse
radixJoinKeepsCoarse = Radix.joinAddressRoot

-- Genuine tower n+1 uses the ENTIRE previous carrier as indices,
-- not three extra hypervoxel coordinates or three seam legs.
selfIndexedStepIsFunctionSpace :
  (n : Nat) →
  Tower.SelfIndexedCarrier (suc n) ≡
    (Tower.SelfIndexedCarrier n → Fin 9)
selfIndexedStepIsFunctionSpace n = refl

-- A level-one nine-axis ternary profile shares cardinality with H369;
-- the semantic chart is NOT an identity between the two records.
nineAxisProfileCountIsFull369 :
  Pareto.ternaryObjectiveProfileCount 1 ≡ H.hyperfabricStateCount
nineAxisProfileCountIsFull369 =
  Pareto.levelOneTernaryProfilesMatchBase369FabricCount

-- Consumer factorisation is already canonically crosswalked by
-- FactorisationSpineCrosswalkExact; do not replace its proof calculus.
