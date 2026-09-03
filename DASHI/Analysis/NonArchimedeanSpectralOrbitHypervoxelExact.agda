module DASHI.Analysis.NonArchimedeanSpectralOrbitHypervoxelExact where

------------------------------------------------------------------------
-- NON-ARCHIMEDEAN SPECTRAL ORBIT HYPERVOXEL
--
-- Cross-pollination target:
--   sneed-and-feed/adelic-spectral-zeta
--   formalization/Formalization/Dynamics/SpectralCircle.lean
--   formalization/Formalization/Dynamics/CyclotomicProduct.lean
--   formalization/Formalization/Spectral/SchreierDynamicalTrace.lean
--
-- This owner deliberately separates:
--   * character/orbit transport,
--   * local multiplicative weight,
--   * return support,
--   * orbit-product amplitude,
--   * trace consumption,
--   * spatial-block same-object transport.
--
-- The external Lean repo proves several algebraic pieces unconditionally, but
-- the spatial twisted-block bridge is carried by TwistedBlockHypothesis.  DASHI
-- therefore imports the architecture without silently identifying the abstract
-- monomial character operator with the spatial S_n block.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set; Set₁)

------------------------------------------------------------------------
-- Source/proof-strength ledger.
------------------------------------------------------------------------

data ProofStrength : Set where
  kernelTheorem : ProofStrength
  conditionalTheorem : ProofStrength
  proseClaim : ProofStrength
  mismatchDetected : ProofStrength

record SourceClaimReceipt : Set where
  constructor sourceClaimReceipt
  field
    sourceRepository : String
    sourcePath : String
    sourceDeclaration : String
    strength : ProofStrength
    sameObjectWeldRequired : Bool

repo : String
repo = "sneed-and-feed/adelic-spectral-zeta"

charActionReceipt : SourceClaimReceipt
charActionReceipt = sourceClaimReceipt
  repo
  "formalization/Formalization/Dynamics/SpectralCircle.lean"
  "collatzDirMatrix_char_action"
  kernelTheorem
  false

orderThreeReceipt : SourceClaimReceipt
orderThreeReceipt = sourceClaimReceipt
  repo
  "formalization/Formalization/Dynamics/SpectralCircle.lean"
  "order_three_mod_pow_two"
  kernelTheorem
  false

cyclotomicProductReceipt : SourceClaimReceipt
cyclotomicProductReceipt = sourceClaimReceipt
  repo
  "formalization/Formalization/Dynamics/CyclotomicProduct.lean"
  "W_1_mul_W_2_eq_two"
  kernelTheorem
  false

traceFixedPointReceipt : SourceClaimReceipt
traceFixedPointReceipt = sourceClaimReceipt
  repo
  "formalization/Formalization/Spectral/SchreierDynamicalTrace.lean"
  "directed_trace_eq_fixed_point_sum"
  kernelTheorem
  false

traceVanishingReceipt : SourceClaimReceipt
traceVanishingReceipt = sourceClaimReceipt
  repo
  "formalization/Formalization/Spectral/SchreierDynamicalTrace.lean"
  "directed_trace_odd_vanishes"
  kernelTheorem
  false

spatialSpectralCircleReceipt : SourceClaimReceipt
spatialSpectralCircleReceipt = sourceClaimReceipt
  repo
  "formalization/Formalization/Dynamics/SpectralCircle.lean"
  "spectral_circle"
  conditionalTheorem
  true

------------------------------------------------------------------------
-- Generic fibre/hypervoxel presentation.
------------------------------------------------------------------------

record SpectralOrbitFabric : Set₁ where
  field
    Level : Set
    CharacterIndex : Set
    Weight : Set
    OrbitAmplitude : Set
    TraceAmplitude : Set

    next : CharacterIndex → CharacterIndex
    localWeight : CharacterIndex → Weight
    orbitAmplitude : CharacterIndex → OrbitAmplitude
    traceAmplitude : CharacterIndex → TraceAmplitude

record SpectralOrbitHypervoxel (F : SpectralOrbitFabric) : Set where
  constructor spectralOrbitHypervoxel
  field
    level : SpectralOrbitFabric.Level F
    index : SpectralOrbitFabric.CharacterIndex F
    transportedIndex : SpectralOrbitFabric.CharacterIndex F
    weight : SpectralOrbitFabric.Weight F
    returnSupport : Bool
    orbitProduct : SpectralOrbitFabric.OrbitAmplitude F
    traceContribution : SpectralOrbitFabric.TraceAmplitude F

------------------------------------------------------------------------
-- Producer receipts keep support and amplitude separate.
------------------------------------------------------------------------

record OrbitTransportReceipt
  (F : SpectralOrbitFabric)
  (v : SpectralOrbitHypervoxel F) : Set where
  field
    transportMatchesNext :
      SpectralOrbitHypervoxel.transportedIndex v
      ≡ SpectralOrbitFabric.next F (SpectralOrbitHypervoxel.index v)

record LocalWeightReceipt
  (F : SpectralOrbitFabric)
  (v : SpectralOrbitHypervoxel F) : Set where
  field
    weightMatchesLocalWeight :
      SpectralOrbitHypervoxel.weight v
      ≡ SpectralOrbitFabric.localWeight F (SpectralOrbitHypervoxel.index v)

record OrbitAmplitudeReceipt
  (F : SpectralOrbitFabric)
  (v : SpectralOrbitHypervoxel F) : Set where
  field
    orbitProductMatchesProducer :
      SpectralOrbitHypervoxel.orbitProduct v
      ≡ SpectralOrbitFabric.orbitAmplitude F (SpectralOrbitHypervoxel.index v)

record TraceAmplitudeReceipt
  (F : SpectralOrbitFabric)
  (v : SpectralOrbitHypervoxel F) : Set where
  field
    traceMatchesProducer :
      SpectralOrbitHypervoxel.traceContribution v
      ≡ SpectralOrbitFabric.traceAmplitude F (SpectralOrbitHypervoxel.index v)

------------------------------------------------------------------------
-- Return support is an independent selector coordinate.
------------------------------------------------------------------------

record ReturnSupportBoundary : Set where
  constructor returnSupportBoundary
  field
    orbitExistsImpliesReturn : Bool
    nonReturnCanStillCarryWeight : Bool
    traceConsumesReturnSupport : Bool

canonicalReturnSupportBoundary : ReturnSupportBoundary
canonicalReturnSupportBoundary =
  returnSupportBoundary false true true

------------------------------------------------------------------------
-- Signed/conjugate orbit cancellation must happen before norming.
------------------------------------------------------------------------

record PairedOrbitCancellationBoundary : Set where
  constructor pairedOrbitCancellationBoundary
  field
    twoOrbitProductsMayBeIndividuallyNonzero : Bool
    signedFirstReturnTraceMayCancel : Bool
    normBeforePairingPreservesCancellation : Bool
    orbitProductMagnitudeDeterminesSignedTrace : Bool

canonicalPairedOrbitCancellationBoundary : PairedOrbitCancellationBoundary
canonicalPairedOrbitCancellationBoundary =
  pairedOrbitCancellationBoundary true true false false

------------------------------------------------------------------------
-- Cyclotomic product theorem firewall.
--
-- In the external Lean declaration W_1_mul_W_2_eq_two, the negative-orbit
-- hypothesis is syntactically named _h_neg and is not used in the proof.
-- Therefore that theorem owns the product over a disjoint partition of all odd
-- residues; it does not by itself establish that the two partition pieces are
-- precisely the two multiplication-by-3 orbits.  The orbit theorem is a
-- separate producer and must be welded separately.
------------------------------------------------------------------------

record CyclotomicOrbitWeldBoundary : Set where
  constructor cyclotomicOrbitWeldBoundary
  field
    totalOddCyclotomicProductIsSourceTheorem : Bool
    productTheoremAloneIdentifiesThreeOrbits : Bool
    orbitStructureNeedsSeparateProducer : Bool
    productAndOrbitMayBeWeldedAfterBothReceipts : Bool

canonicalCyclotomicOrbitWeldBoundary : CyclotomicOrbitWeldBoundary
canonicalCyclotomicOrbitWeldBoundary =
  cyclotomicOrbitWeldBoundary true false true true

------------------------------------------------------------------------
-- Spatial/character same-object firewall.
------------------------------------------------------------------------

record SpatialCharacterWeldBoundary : Set where
  constructor spatialCharacterWeldBoundary
  field
    characterMonomialActionIsUnconditional : Bool
    spatialTwistedBlockIdentificationIsUnconditional : Bool
    twistedBlockHypothesisRequired : Bool
    spectralCircleMayCrossWithoutWeld : Bool

canonicalSpatialCharacterWeldBoundary : SpatialCharacterWeldBoundary
canonicalSpatialCharacterWeldBoundary =
  spatialCharacterWeldBoundary true false true false

------------------------------------------------------------------------
-- Exact cross-pollination summary.
------------------------------------------------------------------------

record NonArchimedeanSpectralCrossPollination : Set where
  constructor nonArchimedeanSpectralCrossPollination
  field
    orbitAndWeightRemainSeparateFibres : Bool
    returnSupportPrecedesTraceAmplitude : Bool
    signedPairingPrecedesNorming : Bool
    cyclotomicProductDoesNotCreateOrbitIdentity : Bool
    spatialBlockNeedsSameObjectWeld : Bool
    hypervoxelConsumerMayRecombineAfterReceipts : Bool

canonicalNonArchimedeanSpectralCrossPollination :
  NonArchimedeanSpectralCrossPollination
canonicalNonArchimedeanSpectralCrossPollination =
  nonArchimedeanSpectralCrossPollination
    true true true true true true

------------------------------------------------------------------------
-- Small exact projection theorems, useful as regression hooks.
------------------------------------------------------------------------

orbitWeightSeparationIsCanonical :
  NonArchimedeanSpectralCrossPollination.orbitAndWeightRemainSeparateFibres
    canonicalNonArchimedeanSpectralCrossPollination
  ≡ true
orbitWeightSeparationIsCanonical = refl

spatialWeldIsFailClosed :
  SpatialCharacterWeldBoundary.spectralCircleMayCrossWithoutWeld
    canonicalSpatialCharacterWeldBoundary
  ≡ false
spatialWeldIsFailClosed = refl

normBeforePairingIsRejected :
  PairedOrbitCancellationBoundary.normBeforePairingPreservesCancellation
    canonicalPairedOrbitCancellationBoundary
  ≡ false
normBeforePairingIsRejected = refl
