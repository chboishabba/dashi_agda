module DASHI.Cognition.PNF.X369RecursiveHypervoxelPantsSameObjectExact where

-- Full 369 hypervoxel + original 13-stage sheaf + original pants seam
-- as views of ONE retained typed state. Existing owners, not new ontology.
-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Kernel deliberately deferred. No claim that a native neural history
-- already inhabits this packet without a source-owned admission map.
open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
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
import DASHI.Reasoning.TypedHyperfabricPantsNonvacuousSeamQuotientExact as Seam
import DASHI.Reasoning.TypedHyperfabricPantsSignatureCompletenessExact as Match
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants

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

  actualPants13 : Packet → DASHI.Topology.TernaryPantsFrontierExact.PantsPath 13
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
