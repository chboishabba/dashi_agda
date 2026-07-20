module Ontology.DNA.ChemistrySheetCrossPollination where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (cong)

open import Ontology.DNA.Supervoxel4Adic using
  (Base; FlatDNA256)
open import Ontology.DNA.ChemistryQuotient using
  (ChemistryFeature)
open import Ontology.DNA.ChemistryUVCoordinates using
  (UVCoordinates; encodeUV; decodeUV; decodeEncode; encodeFeature256)
open import Ontology.DNA.ChemistryConcrete using
  (featureMapConcrete; thermoKernelConcrete; admissibleConcrete)
open import Ontology.DNA.ChemistrySheetHamiltonian using
  (Signed; SheetCoordinates; sheetCoordinatesOf; chemistryHamiltonian)
open import Ontology.DNA.ChemistrySheetTowerBoundary using
  (SheetRepresentation; baseCoordinatePair; coefficientSheet;
   expandedDetailField; scalarEnergySummary; CarrierGrowthLaw;
   fixedFourWayNesting; tetrationalComposition)

------------------------------------------------------------------------
-- Cross-pollinated DNA architecture.
--
-- This module joins the existing exact DNA/UV/quotient lane to the signed
-- chemistry-energy and future sheet-tower lanes while preserving the semantic
-- boundary between them.

------------------------------------------------------------------------
-- Information authority carried by each representation.

data InformationStatus : Set where
  exactCoordinate : InformationStatus
  quotientObservable : InformationStatus
  quantizedCandidate : InformationStatus
  renderedSummary : InformationStatus

record LayerDescriptor : Set where
  constructor layerDescriptor
  field
    representation : SheetRepresentation
    status : InformationStatus

rawUVLayer : LayerDescriptor
rawUVLayer = layerDescriptor baseCoordinatePair exactCoordinate

signedChemistryLayer : LayerDescriptor
signedChemistryLayer = layerDescriptor baseCoordinatePair quantizedCandidate

futureCoefficientLayer : LayerDescriptor
futureCoefficientLayer = layerDescriptor coefficientSheet quotientObservable

futureExpandedLayer : LayerDescriptor
futureExpandedLayer = layerDescriptor expandedDetailField quotientObservable

energySummaryLayer : LayerDescriptor
energySummaryLayer = layerDescriptor scalarEnergySummary renderedSummary

------------------------------------------------------------------------
-- Exact carrier -> UV -> chemistry-feature spine.

featureSpineAgrees :
  (xs : FlatDNA256) → encodeFeature256 xs ≡ featureMapConcrete xs
featureSpineAgrees xs = refl

uvRoundTrip256 :
  (xs : FlatDNA256) → decodeUV (encodeUV xs) ≡ xs
uvRoundTrip256 = decodeEncode

------------------------------------------------------------------------
-- The current signed chemistry coordinates are obtained through the exact UV
-- chart, but this does not make them a multiscale detail decomposition.

signedFromUV : ∀ {n} → UVCoordinates n → SheetCoordinates n
signedFromUV uv = sheetCoordinatesOf (decodeUV uv)

signedFromUV-section :
  ∀ {n} (xs : Vec Base n) →
  signedFromUV (encodeUV xs) ≡ sheetCoordinatesOf xs
signedFromUV-section xs = cong sheetCoordinatesOf (decodeEncode xs)

------------------------------------------------------------------------
-- One canonical integration surface for downstream consumers.

record ChemistryCoordinateEnergySpine : Set₁ where
  field
    Raw : Set
    ExactCoordinates : Set
    Feature : Set
    SignedCoordinates : Set

    encodeExact : Raw → ExactCoordinates
    decodeExact : ExactCoordinates → Raw
    feature : Raw → Feature
    signedCoordinates : Raw → SignedCoordinates
    localThermoEnergy : Raw → Nat
    aggregateChemistryEnergy : Raw → Nat
    admissible : Raw → Bool

    exactRoundTrip : (x : Raw) → decodeExact (encodeExact x) ≡ x
    featureCompatibility :
      (x : Raw) → feature x ≡ encodeFeature256 x

chemistryCoordinateEnergySpine : ChemistryCoordinateEnergySpine
chemistryCoordinateEnergySpine = record
  { Raw = FlatDNA256
  ; ExactCoordinates = UVCoordinates 256
  ; Feature = ChemistryFeature
  ; SignedCoordinates = SheetCoordinates 256
  ; encodeExact = encodeUV
  ; decodeExact = decodeUV
  ; feature = featureMapConcrete
  ; signedCoordinates = sheetCoordinatesOf
  ; localThermoEnergy = thermoKernelConcrete
  ; aggregateChemistryEnergy = chemistryHamiltonian
  ; admissible = admissibleConcrete
  ; exactRoundTrip = decodeEncode
  ; featureCompatibility = λ x → refl
  }

------------------------------------------------------------------------
-- What can be reused from the broader DASHI formalism.

record SheetCrossPollinationBoundary : Set where
  field
    exactUVFeedsQuotient : Bool
    exactUVFeedsSignedEnergy : Bool
    signedEnergyIsAlreadyDetailTower : Bool
    fixedCarrierNestingDeterminesTetration : Bool
    ternaryQuantizationNeedsErrorBound : Bool
    phaseEigenspaceNeedsOperator : Bool
    chemistryTermsNeedNotAllBeQuadratic : Bool

sheetCrossPollinationBoundary : SheetCrossPollinationBoundary
sheetCrossPollinationBoundary = record
  { exactUVFeedsQuotient = true
  ; exactUVFeedsSignedEnergy = true
  ; signedEnergyIsAlreadyDetailTower = false
  ; fixedCarrierNestingDeterminesTetration = false
  ; ternaryQuantizationNeedsErrorBound = true
  ; phaseEigenspaceNeedsOperator = true
  ; chemistryTermsNeedNotAllBeQuadratic = true
  }

------------------------------------------------------------------------
-- Growth-law handoff.
--
-- The existing carrier supplies the finite four-way instance.  A future
-- tetrational activation-sheet construction must separately supply the
-- recursive composition law and show how its levels analyse and reconstruct
-- this DNA signal carrier.

currentCarrierGrowth : CarrierGrowthLaw
currentCarrierGrowth = fixedFourWayNesting

futureTetrationalGrowthCandidate : CarrierGrowthLaw
futureTetrationalGrowthCandidate = tetrationalComposition
