module DASHI.Analysis.NonArchimedeanSpectralBidiObligationExact where

------------------------------------------------------------------------
-- Reverse / BIDI obligation compiler for the non-Archimedean spectral lane.
--
-- Generic and arithmetic producers already recovered in the repo are pruned
-- from reverse search.  In particular:
--
--   * primitive half-turn -> -1 is upstream reusable;
--   * odd-character <-> tau-odd compiles from that half-turn and parity;
--   * the strong source theorem `three_pow_two_pow` compiles the full-orbit sum
--     to the dyadic half period;
--   * C2=-C1 plus finite-product algebra compiles W2=-W1 and W1+W2=0;
--   * existing matrix faithfulness compiles literal matrix equality from basis
--     action equality.
--
-- Thus downstream spatial claims reopen only same-object character wiring,
-- canonical orbit receipts, and the appropriate same-label magnitude/period.
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
    "corrected odd-character DFT instantiation + twisted-coordinate same-object weld + canonical odd-orbit receipts + same-label magnitude receipt"
    true false false false

spatialTwistedPowerClaim : BidiClaim
spatialTwistedPowerClaim =
  bidiClaim spatialTwistedPower
    "spatial twisted-block doubled-return power equals minus two identity"
    "corrected odd-character DFT instantiation + twisted-coordinate same-object weld + canonical odd-orbit period; signed orbit weight now compiles from strong three-power arithmetic"
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
  needInstantiateCorrectOddCharacterDFT : MissingObligation
  needArithmeticOddOrbitReceipts : MissingObligation
  needTwistedCoordinateOddCharacterIdentification : MissingObligation
  needCompleteCharacterBasisActionEquality : MissingObligation
  needConcreteDFTMonomialMatrixEquality : MissingObligation
  needConcretePeriodAttachment : MissingObligation
  needConcreteOrbitMagnitudeAttachment : MissingObligation
  needOrbitPartitionWeld : MissingObligation
  needGraphToDecompositionProducer : MissingObligation
  needDepthDecayProducer : MissingObligation
  needBoundaryEntropySameObjectWeld : MissingObligation
  needModelLevelRoPEConsumerTheorem : MissingObligation
  noMissingObligation : MissingObligation

compileMissing : ClaimKind → List MissingObligation
compileMissing spatialSpectralCircle =
  needInstantiateCorrectOddCharacterDFT ∷
  needArithmeticOddOrbitReceipts ∷
  needTwistedCoordinateOddCharacterIdentification ∷
  needCompleteCharacterBasisActionEquality ∷
  needConcretePeriodAttachment ∷
  needConcreteOrbitMagnitudeAttachment ∷
  []
compileMissing spatialTwistedPower =
  needInstantiateCorrectOddCharacterDFT ∷
  needArithmeticOddOrbitReceipts ∷
  needTwistedCoordinateOddCharacterIdentification ∷
  needCompleteCharacterBasisActionEquality ∷
  needConcretePeriodAttachment ∷
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
    primitiveHalfTurnShouldRemainOnSearchFrontier : Bool
    signedOrbitCancellationShouldRemainOnSearchFrontier : Bool
    explicitComplexPhaseValuesRequiredForMinusTwo : Bool

canonicalBidiFirewall : BidiFirewall
canonicalBidiFirewall =
  bidiFirewall false false false false false false false false false false false

spatialSpectralCircleExactCutset :
  compileMissing (kind spectralCircleSpatialClaim)
  ≡ needInstantiateCorrectOddCharacterDFT ∷
    needArithmeticOddOrbitReceipts ∷
    needTwistedCoordinateOddCharacterIdentification ∷
    needCompleteCharacterBasisActionEquality ∷
    needConcretePeriodAttachment ∷
    needConcreteOrbitMagnitudeAttachment ∷
    []
spatialSpectralCircleExactCutset = refl

spatialPowerSignedLeafIsNowPruned :
  compileMissing (kind spatialTwistedPowerClaim)
  ≡ needInstantiateCorrectOddCharacterDFT ∷
    needArithmeticOddOrbitReceipts ∷
    needTwistedCoordinateOddCharacterIdentification ∷
    needCompleteCharacterBasisActionEquality ∷
    needConcretePeriodAttachment ∷
    []
spatialPowerSignedLeafIsNowPruned = refl

compiledMatrixEqualityIsPrunedFromSearch :
  BidiFirewall.compiledMatrixEqualityShouldRemainOnSearchFrontier
    canonicalBidiFirewall
  ≡ false
compiledMatrixEqualityIsPrunedFromSearch = refl

primitiveHalfTurnIsPrunedFromSearch :
  BidiFirewall.primitiveHalfTurnShouldRemainOnSearchFrontier
    canonicalBidiFirewall
  ≡ false
primitiveHalfTurnIsPrunedFromSearch = refl

signedOrbitCancellationIsPrunedFromSearch :
  BidiFirewall.signedOrbitCancellationShouldRemainOnSearchFrontier
    canonicalBidiFirewall
  ≡ false
signedOrbitCancellationIsPrunedFromSearch = refl

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
