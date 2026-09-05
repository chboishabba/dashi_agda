module DASHI.Analysis.NonArchimedeanSpectralBidiObligationExact where

------------------------------------------------------------------------
-- Reverse / BIDI obligation compiler for the non-Archimedean spectral lane.
--
-- All generic Fourier, matrix, orbit, sign, and binary-sheet mathematics are
-- now owned or reusable in-repo.  The finite spectral core therefore reopens
-- one foreign-source producer only:
--
--   concrete Lean ZMod-2 sheet model
--      -> DASHI binary-sheet/twisted-restriction adapter.
--
-- From that single adapter the corrected odd-character DFT, complete basis
-- action, literal monomial matrix equality, spatial spectrum, trace, and power
-- consumers are compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)


data ClaimKind : Set where
  spatialSpectralCircle : ClaimKind
  spatialTwistedPower : ClaimKind
  orbitProduct : ClaimKind
  arbitraryDagCover : ClaimKind
  depthDecaySparsity : ClaimKind
  contractedBoundaryEntropy : ClaimKind
  ropeOptimality : ClaimKind

record BidiClaim : Set where
  constructor bidiClaim
  field
    kind : ClaimKind
    claimName : String
    producerName : String
    theoremExists : Bool
    sameObjectWeldOwned : Bool
    advertisedStrengthOwned : Bool
    promotionAllowed : Bool

open BidiClaim public

spectralCircleSpatialClaim : BidiClaim
spectralCircleSpatialClaim =
  bidiClaim spatialSpectralCircle
    "spatial twisted-block spectral circle"
    "single concrete source sheet adapter for D'_matrix/twistedDirMatrix"
    true false false false

spatialTwistedPowerClaim : BidiClaim
spatialTwistedPowerClaim =
  bidiClaim spatialTwistedPower
    "spatial twisted-block doubled-return power equals minus two identity"
    "same single concrete source sheet adapter; orbit/sign/power machinery already compiles"
    true false false false

orbitProductClaim : BidiClaim
orbitProductClaim =
  bidiClaim orbitProduct
    "two x3 orbit products multiply to two"
    "odd-residue cyclotomic product + canonical two-orbit partition compiler"
    true true true true

multiPrimeCoverClaim : BidiClaim
multiPrimeCoverClaim =
  bidiClaim arbitraryDagCover
    "arbitrary DAG admits multi-prime adelic cover"
    "construction of MultiPrimeTreeDecomposition from graph hypotheses"
    true false false false

multiPrimeSparsityClaim : BidiClaim
multiPrimeSparsityClaim =
  bidiClaim depthDecaySparsity
    "depth-decaying active attention fraction"
    "nontrivial quantitative bound connecting routing depth to active set size"
    true false false false

holographicAreaClaim : BidiClaim
holographicAreaClaim =
  bidiClaim contractedBoundaryEntropy
    "contracted boundary-state entropy equals cut size times log two"
    "same-object equality between contracted density-state entropy and the existential entropy scalar"
    true false false false

ropeOptimalityClaim : BidiClaim
ropeOptimalityClaim =
  bidiClaim ropeOptimality
    "RoPE medoid compression is transformer-optimal"
    "model-level loss / fidelity theorem built on the geometric invariance theorem"
    true false false false


data MissingObligation : Set where
  needConcreteSourceSheetAdapter : MissingObligation
  needConcreteDFTMonomialMatrixEquality : MissingObligation
  needGraphToDecompositionProducer : MissingObligation
  needDepthDecayProducer : MissingObligation
  needBoundaryEntropySameObjectWeld : MissingObligation
  needModelLevelRoPEConsumerTheorem : MissingObligation
  noMissingObligation : MissingObligation

compileMissing : ClaimKind → List MissingObligation
compileMissing spatialSpectralCircle =
  needConcreteSourceSheetAdapter ∷ []
compileMissing spatialTwistedPower =
  needConcreteSourceSheetAdapter ∷ []
compileMissing orbitProduct = []
compileMissing arbitraryDagCover = needGraphToDecompositionProducer ∷ []
compileMissing depthDecaySparsity = needDepthDecayProducer ∷ []
compileMissing contractedBoundaryEntropy = needBoundaryEntropySameObjectWeld ∷ []
compileMissing ropeOptimality = needModelLevelRoPEConsumerTheorem ∷ []

matrixEqualityIsCompilerOutput : MissingObligation
matrixEqualityIsCompilerOutput = needConcreteDFTMonomialMatrixEquality

record BidiFirewall : Set where
  constructor bidiFirewall
  field
    theoremNameImpliesAdvertisedStrength : Bool
    theoremExistsImpliesSameObjectWeld : Bool
    conditionalConsumerImpliesProducer : Bool
    architecturalAnalogyImpliesTheoremTransport : Bool
    finalMagnitudeHypothesisMayCountAsItsOwnDerivation : Bool
    compiledMatrixEqualityShouldRemainOnSearchFrontier : Bool
    genericDFTShouldRemainOnSearchFrontier : Bool
    canonicalOrbitReceiptsShouldRemainOnSearchFrontier : Bool
    signedOrbitCancellationShouldRemainOnSearchFrontier : Bool
    genericBinarySheetEquivalenceShouldRemainOnSearchFrontier : Bool

canonicalBidiFirewall : BidiFirewall
canonicalBidiFirewall =
  bidiFirewall false false false false false false false false false false

spatialSpectralCircleSingleAdapterCutset :
  compileMissing (kind spectralCircleSpatialClaim)
  ≡ needConcreteSourceSheetAdapter ∷ []
spatialSpectralCircleSingleAdapterCutset = refl

spatialPowerSharesSingleAdapter :
  compileMissing (kind spatialTwistedPowerClaim)
  ≡ needConcreteSourceSheetAdapter ∷ []
spatialPowerSharesSingleAdapter = refl

compiledMatrixEqualityIsPrunedFromSearch :
  BidiFirewall.compiledMatrixEqualityShouldRemainOnSearchFrontier
    canonicalBidiFirewall
  ≡ false
compiledMatrixEqualityIsPrunedFromSearch = refl

canonicalOrbitSearchIsPruned :
  BidiFirewall.canonicalOrbitReceiptsShouldRemainOnSearchFrontier
    canonicalBidiFirewall
  ≡ false
canonicalOrbitSearchIsPruned = refl

signedOrbitSearchIsPruned :
  BidiFirewall.signedOrbitCancellationShouldRemainOnSearchFrontier
    canonicalBidiFirewall
  ≡ false
signedOrbitSearchIsPruned = refl

genericBinarySheetSearchIsPruned :
  BidiFirewall.genericBinarySheetEquivalenceShouldRemainOnSearchFrontier
    canonicalBidiFirewall
  ≡ false
genericBinarySheetSearchIsPruned = refl

orbitProductIsPromotable :
  compileMissing (kind orbitProductClaim) ≡ []
orbitProductIsPromotable = refl

multiPrimeCoverNeedsProducer :
  compileMissing (kind multiPrimeCoverClaim)
  ≡ needGraphToDecompositionProducer ∷ []
multiPrimeCoverNeedsProducer = refl

multiPrimeSparsityNeedsQuantitativeProducer :
  compileMissing (kind multiPrimeSparsityClaim)
  ≡ needDepthDecayProducer ∷ []
multiPrimeSparsityNeedsQuantitativeProducer = refl

holographicClaimNeedsSameObjectWeld :
  compileMissing (kind holographicAreaClaim)
  ≡ needBoundaryEntropySameObjectWeld ∷ []
holographicClaimNeedsSameObjectWeld = refl

ropeOptimalityNeedsModelConsumer :
  compileMissing (kind ropeOptimalityClaim)
  ≡ needModelLevelRoPEConsumerTheorem ∷ []
ropeOptimalityNeedsModelConsumer = refl
