module DASHI.Analysis.NonArchimedeanSpectralBidiObligationExact where

------------------------------------------------------------------------
-- Reverse / BIDI obligation compiler for the non-Archimedean spectral lane.
--
-- Source correction: the currently checked F_(2^(n-2)) tensor I_2 transform
-- after an arbitrary Fin product reindex is not yet the odd-character Fourier
-- transform.  Downstream spatial claims therefore reopen the semantic
-- odd-character rechart, not generic DFT algebra or raw matrix expansion.
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
    "odd-character Fourier rechart + half-period classifier + arithmetic odd-orbit receipts + same-label magnitude receipt"
    true false false false

spatialTwistedPowerClaim : BidiClaim
spatialTwistedPowerClaim =
  bidiClaim spatialTwistedPower
    "spatial twisted-block doubled-return power equals minus two identity"
    "spatial character weld + orbit period + paired product two + orbit cancellation sum zero"
    true false false false

orbitProductClaim : BidiClaim
orbitProductClaim =
  bidiClaim orbitProduct
    "two x3 orbit products multiply to two"
    "odd-residue cyclotomic product + separate x3 orbit partition receipt"
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
  needPrimitiveHalfTurnInstantiation : MissingObligation
  needOddCharacterFourierRechart : MissingObligation
  needArithmeticOddOrbitReceipts : MissingObligation
  needTwistedCoordinateOddCharacterIdentification : MissingObligation
  needCompleteCharacterBasisActionEquality : MissingObligation
  needConcreteDFTMonomialMatrixEquality : MissingObligation
  needConcretePeriodAttachment : MissingObligation
  needConcreteOrbitMagnitudeAttachment : MissingObligation
  needOrbitCancellationSumZero : MissingObligation
  needOrbitPartitionWeld : MissingObligation
  needGraphToDecompositionProducer : MissingObligation
  needDepthDecayProducer : MissingObligation
  needBoundaryEntropySameObjectWeld : MissingObligation
  needModelLevelRoPEConsumerTheorem : MissingObligation
  noMissingObligation : MissingObligation

compileMissing : ClaimKind → List MissingObligation
compileMissing spatialSpectralCircle =
  needPrimitiveHalfTurnInstantiation ∷
  needOddCharacterFourierRechart ∷
  needArithmeticOddOrbitReceipts ∷
  needTwistedCoordinateOddCharacterIdentification ∷
  needCompleteCharacterBasisActionEquality ∷
  needConcretePeriodAttachment ∷
  needConcreteOrbitMagnitudeAttachment ∷
  []
compileMissing spatialTwistedPower =
  needOddCharacterFourierRechart ∷
  needArithmeticOddOrbitReceipts ∷
  needTwistedCoordinateOddCharacterIdentification ∷
  needCompleteCharacterBasisActionEquality ∷
  needConcretePeriodAttachment ∷
  needOrbitCancellationSumZero ∷
  []
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
    genericInfrastructureMayReplaceConcreteAttachment : Bool
    finalMagnitudeHypothesisMayCountAsItsOwnDerivation : Bool
    compiledMatrixEqualityShouldRemainOnSearchFrontier : Bool
    arbitraryUnitaryDFTMayCountAsOddCharacterDFT : Bool
    explicitComplexPhaseValuesRequiredForMinusTwo : Bool

canonicalBidiFirewall : BidiFirewall
canonicalBidiFirewall =
  bidiFirewall false false false false false false false false false

spatialSpectralCircleExactCutset :
  compileMissing (kind spectralCircleSpatialClaim)
  ≡ needPrimitiveHalfTurnInstantiation ∷
    needOddCharacterFourierRechart ∷
    needArithmeticOddOrbitReceipts ∷
    needTwistedCoordinateOddCharacterIdentification ∷
    needCompleteCharacterBasisActionEquality ∷
    needConcretePeriodAttachment ∷
    needConcreteOrbitMagnitudeAttachment ∷
    []
spatialSpectralCircleExactCutset = refl

spatialPowerNeedsOnlyMinimalSignProducer :
  compileMissing (kind spatialTwistedPowerClaim)
  ≡ needOddCharacterFourierRechart ∷
    needArithmeticOddOrbitReceipts ∷
    needTwistedCoordinateOddCharacterIdentification ∷
    needCompleteCharacterBasisActionEquality ∷
    needConcretePeriodAttachment ∷
    needOrbitCancellationSumZero ∷
    []
spatialPowerNeedsOnlyMinimalSignProducer = refl

compiledMatrixEqualityIsPrunedFromSearch :
  BidiFirewall.compiledMatrixEqualityShouldRemainOnSearchFrontier
    canonicalBidiFirewall
  ≡ false
compiledMatrixEqualityIsPrunedFromSearch = refl

arbitraryUnitaryDoesNotSupplyCharacterSemantics :
  BidiFirewall.arbitraryUnitaryDFTMayCountAsOddCharacterDFT
    canonicalBidiFirewall
  ≡ false
arbitraryUnitaryDoesNotSupplyCharacterSemantics = refl

explicitPhaseValuesNotRequiredForPower :
  BidiFirewall.explicitComplexPhaseValuesRequiredForMinusTwo
    canonicalBidiFirewall
  ≡ false
explicitPhaseValuesNotRequiredForPower = refl

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
