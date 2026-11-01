module DASHI.Visual.ColourPerceptionCrossPollination where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AnimalSenseObservationThreadDischarge as AnimalSense
import DASHI.Biology.ObserverPerceptualManifoldResidual as Observer
import DASHI.Combinatorics.TriadicVideoCodecObservationQuotient as Codec
import DASHI.Crypto.RSABTResidueBraidHypervoxelBoundary as RSABT
import DASHI.Visual.ColourPerceptionDASHI as Colour

------------------------------------------------------------------------
-- Cross-pollination boundary for the new visual-colour lane.
--
-- This module does not identify colour perception with any one existing
-- formalism.  It records the invariant-scoped relationships that are useful:
--
--   * ObserverPerceptualManifoldResidual supplies observer-fibre projection,
--     residual-defect, and blocked-phenomenal-closure structure.
--   * TriadicVideoCodecObservationQuotient supplies an exact signed residual /
--     balanced-ternary refinement pattern, not a perception theorem.
--   * RSABTResidueBraidHypervoxelBoundary supplies a candidate-only precedent
--     for combining BT chamber, braid, visible support, and hypervoxel labels.
--   * ColourPerceptionDASHI supplies the actual visual-colour carrier, MCCP,
--     PCCS, RGBA, and CMYKA surfaces.
--
-- In particular, an MCCP cell is an observer-fibre quotient coordinate.  It is
-- not a universal colour, a recovered quale, or a claim that human vision has
-- exactly twenty-seven phenomenal states.

------------------------------------------------------------------------
-- Structural correspondences retained from the neighbouring formalisms.

data ColourCrossPollinationLayer : Set where
  observerFibreLayer : ColourCrossPollinationLayer
  opponentResidueLayer : ColourCrossPollinationLayer
  mccpPartitionLayer : ColourCrossPollinationLayer
  projectionResidualLayer : ColourCrossPollinationLayer
  projectionDefectLayer : ColourCrossPollinationLayer
  hypervoxelSupportLayer : ColourCrossPollinationLayer
  balancedTernaryBraidLayer : ColourCrossPollinationLayer
  colourCoordinateProjectionLayer : ColourCrossPollinationLayer
  phenomenalClosureBoundaryLayer : ColourCrossPollinationLayer

canonicalColourCrossPollinationLayers : List ColourCrossPollinationLayer
canonicalColourCrossPollinationLayers =
  observerFibreLayer
  ∷ opponentResidueLayer
  ∷ mccpPartitionLayer
  ∷ projectionResidualLayer
  ∷ projectionDefectLayer
  ∷ hypervoxelSupportLayer
  ∷ balancedTernaryBraidLayer
  ∷ colourCoordinateProjectionLayer
  ∷ phenomenalClosureBoundaryLayer
  ∷ []

data ColourCrossPollinationBoundary : Set where
  noMCCPAsUniversalPhenomenalState : ColourCrossPollinationBoundary
  noObserverFibreIsomorphism : ColourCrossPollinationBoundary
  noQualiaPreservingColourMap : ColourCrossPollinationBoundary
  noBTGeometryAsNeuroscience : ColourCrossPollinationBoundary
  noCodecAsVisionPhysiology : ColourCrossPollinationBoundary
  noPCCSAsDeviceTruth : ColourCrossPollinationBoundary
  noRGBAOrCMYKAAsPerceptionIdentity : ColourCrossPollinationBoundary
  noCrossSpeciesColourIdentity : ColourCrossPollinationBoundary
  noReceiptlessVisualAuthority : ColourCrossPollinationBoundary

canonicalColourCrossPollinationBoundaries :
  List ColourCrossPollinationBoundary
canonicalColourCrossPollinationBoundaries =
  noMCCPAsUniversalPhenomenalState
  ∷ noObserverFibreIsomorphism
  ∷ noQualiaPreservingColourMap
  ∷ noBTGeometryAsNeuroscience
  ∷ noCodecAsVisionPhysiology
  ∷ noPCCSAsDeviceTruth
  ∷ noRGBAOrCMYKAAsPerceptionIdentity
  ∷ noCrossSpeciesColourIdentity
  ∷ noReceiptlessVisualAuthority
  ∷ []

------------------------------------------------------------------------
-- Typed local anchors into the existing repository.

colourObserverSpecies : Observer.ObserverSpecies
colourObserverSpecies = Observer.humanObserver

colourObserverFibre : Observer.PerceptualFibre
colourObserverFibre = Observer.humanVisionLanguageFibre

colourObserverFibreIsCanonical :
  Observer.fibreFor colourObserverSpecies ≡ colourObserverFibre
colourObserverFibreIsCanonical = refl

colourProjectionResiduals : List Observer.ProjectionResidualKind
colourProjectionResiduals = Observer.canonicalProjectionResiduals

colourProjectionDefects : List Observer.ProjectionDefectKind
colourProjectionDefects = Observer.canonicalProjectionDefects

colourPhenomenalBoundaries : List Observer.PhenomenalBoundary
colourPhenomenalBoundaries = Observer.canonicalPhenomenalBoundaries

colourBalancedTernaryCodecLayer : Codec.CodecPipelineLayer
colourBalancedTernaryCodecLayer = Codec.balancedTernaryPlaneLayer

colourSignedResidualCodecLayer : Codec.CodecPipelineLayer
colourSignedResidualCodecLayer = Codec.signedResidualLayer

colourBTBraidHypervoxelBoundaryStatus :
  RSABT.RSABTResidueBraidHypervoxelBoundaryStatus
colourBTBraidHypervoxelBoundaryStatus =
  RSABT.rsaBtResidueBraidHypervoxelBoundaryRecordedNoPromotion

colourNoQualiaThreadBoundary : AnimalSense.ThreadDischargeBoundary
colourNoQualiaThreadBoundary = AnimalSense.noQualiaRecovery

colourNoCrossSenseThreadBoundary : AnimalSense.ThreadDischargeBoundary
colourNoCrossSenseThreadBoundary =
  AnimalSense.noArbitraryCrossSenseIdentityDischarge

------------------------------------------------------------------------
-- MCCP as an observer-fibre quotient coordinate with retained defects.

record MCCPObserverFibreCoordinate : Set where
  field
    observer : Observer.ObserverSpecies
    fibre : Observer.PerceptualFibre
    fibreMatchesObserver : Observer.fibreFor observer ≡ fibre
    opponentResidue : Colour.OpponentResidue
    mccpCell : Colour.MCCPCell
    mccpCellMatchesResidue :
      Colour.triColourResidueToMCCP opponentResidue ≡ mccpCell
    retainedProjectionResiduals : List Observer.ProjectionResidualKind
    retainedProjectionDefects : List Observer.ProjectionDefectKind
    coordinateReading : String

canonicalMCCPObserverFibreCoordinate : MCCPObserverFibreCoordinate
canonicalMCCPObserverFibreCoordinate =
  record
    { observer = colourObserverSpecies
    ; fibre = colourObserverFibre
    ; fibreMatchesObserver = refl
    ; opponentResidue = Colour.canonicalOpponentResidue
    ; mccpCell = Colour.mccp000
    ; mccpCellMatchesResidue = refl
    ; retainedProjectionResiduals = colourProjectionResiduals
    ; retainedProjectionDefects = colourProjectionDefects
    ; coordinateReading =
        "The MCCP cell is a coarse observer-fibre coordinate with explicit projection residuals and defects; it is not a phenomenal-state identity."
    }

------------------------------------------------------------------------
-- Hypervoxel synthesis: local colour contact plus residual governance.

record GovernedColourHypervoxel : Set where
  field
    hypervoxel : Colour.ColourHypervoxel
    observerCoordinate : MCCPObserverFibreCoordinate
    braid : Colour.BTColourBraid
    residualKinds : List Observer.ProjectionResidualKind
    defectKinds : List Observer.ProjectionDefectKind
    phenomenalBoundaries : List Observer.PhenomenalBoundary
    supportBoundaryStatus :
      RSABT.RSABTResidueBraidHypervoxelBoundaryStatus
    governedReading : String

canonicalGovernedColourHypervoxel : GovernedColourHypervoxel
canonicalGovernedColourHypervoxel =
  record
    { hypervoxel = Colour.canonicalColourHypervoxel
    ; observerCoordinate = canonicalMCCPObserverFibreCoordinate
    ; braid = Colour.canonicalBTColourBraid
    ; residualKinds = colourProjectionResiduals
    ; defectKinds = colourProjectionDefects
    ; phenomenalBoundaries = colourPhenomenalBoundaries
    ; supportBoundaryStatus = colourBTBraidHypervoxelBoundaryStatus
    ; governedReading =
        "A colour hypervoxel carries local opponent/MCCP contact, sparse balanced-ternary correction, observer-fibre residuals, and blocked phenomenal closure."
    }

------------------------------------------------------------------------
-- Cross-pollination certificate.

record ColourCrossPollinationCertificate : Set where
  field
    layers : List ColourCrossPollinationLayer
    layersAreCanonical : layers ≡ canonicalColourCrossPollinationLayers
    boundaries : List ColourCrossPollinationBoundary
    boundariesAreCanonical :
      boundaries ≡ canonicalColourCrossPollinationBoundaries
    observerCoordinate : MCCPObserverFibreCoordinate
    governedHypervoxel : GovernedColourHypervoxel
    mccpUniversalPhenomenalStatePromoted : Bool
    mccpUniversalPhenomenalStatePromotedIsFalse :
      mccpUniversalPhenomenalStatePromoted ≡ false
    observerFibreIsomorphismPromoted : Bool
    observerFibreIsomorphismPromotedIsFalse :
      observerFibreIsomorphismPromoted ≡ false
    btGeometryAsNeurosciencePromoted : Bool
    btGeometryAsNeurosciencePromotedIsFalse :
      btGeometryAsNeurosciencePromoted ≡ false
    codecAsVisionPhysiologyPromoted : Bool
    codecAsVisionPhysiologyPromotedIsFalse :
      codecAsVisionPhysiologyPromoted ≡ false
    crossSurfaceColourIdentityPromoted : Bool
    crossSurfaceColourIdentityPromotedIsFalse :
      crossSurfaceColourIdentityPromoted ≡ false
    certificateReading : String

canonicalColourCrossPollinationCertificate :
  ColourCrossPollinationCertificate
canonicalColourCrossPollinationCertificate =
  record
    { layers = canonicalColourCrossPollinationLayers
    ; layersAreCanonical = refl
    ; boundaries = canonicalColourCrossPollinationBoundaries
    ; boundariesAreCanonical = refl
    ; observerCoordinate = canonicalMCCPObserverFibreCoordinate
    ; governedHypervoxel = canonicalGovernedColourHypervoxel
    ; mccpUniversalPhenomenalStatePromoted = false
    ; mccpUniversalPhenomenalStatePromotedIsFalse = refl
    ; observerFibreIsomorphismPromoted = false
    ; observerFibreIsomorphismPromotedIsFalse = refl
    ; btGeometryAsNeurosciencePromoted = false
    ; btGeometryAsNeurosciencePromotedIsFalse = refl
    ; codecAsVisionPhysiologyPromoted = false
    ; codecAsVisionPhysiologyPromotedIsFalse = refl
    ; crossSurfaceColourIdentityPromoted = false
    ; crossSurfaceColourIdentityPromotedIsFalse = refl
    ; certificateReading =
        "Colour cross-pollination retains observer-fibre projection defects, MCCP coarse contact, hypervoxel locality, and balanced-ternary braid refinement while blocking qualia, neuroscience, and cross-surface identity promotion."
    }
