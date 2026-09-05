module DASHI.Analysis.NonArchimedeanSpectralBidiObligationExact where

------------------------------------------------------------------------
-- Reverse / BIDI obligation compiler for the non-Archimedean spectral lane.
--
-- After reusing all currently owned arithmetic and generic machinery, the
-- finite spectral core has one composite source-specific seam:
--
--   literal Hadamard twisted coordinate
--      <-> tau-odd full function
--      <-> odd-character basis
--      <-> corrected modulated half-size DFT coordinates.
--
-- Everything else now compiles after that seam:
--
--   * canonical two odd orbits from exact order/parity/cardinality;
--   * orbit period from exact order;
--   * orbit magnitude from the existing conditional magnitude theorem;
--   * signed full return from the stronger source `three_pow_two_pow` theorem;
--   * literal monomial matrix equality from complete basis action equality;
--   * spatial spectrum/trace/power transport from the common weld.
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
    "corrected odd-character DFT instantiation + twisted-coordinate/tau-odd same-object weld"
    true false false false

spatialTwistedPowerClaim : BidiClaim
spatialTwistedPowerClaim =
  bidiClaim spatialTwistedPower
    "spatial twisted-block doubled-return power equals minus two identity"
    "same corrected spatial/character weld; orbit period and signed return now compile from owned arithmetic"
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
  needInstantiateCorrectOddCharacterDFT : MissingObligation
  needTwistedCoordinateTauOddFunctionWeld : MissingObligation
  needCompleteCharacterBasisActionEquality : MissingObligation
  needConcreteDFTMonomialMatrixEquality : MissingObligation
  needGraphToDecompositionProducer : MissingObligation
  needDepthDecayProducer : MissingObligation
  needBoundaryEntropySameObjectWeld : MissingObligation
  needModelLevelRoPEConsumerTheorem : MissingObligation
  noMissingObligation : MissingObligation

compileMissing : ClaimKind → List MissingObligation
compileMissing spatialSpectralCircle =
  needInstantiateCorrectOddCharacterDFT ∷
  needTwistedCoordinateTauOddFunctionWeld ∷
  needCompleteCharacterBasisActionEquality ∷
  []
compileMissing spatialTwistedPower =
  needInstantiateCorrectOddCharacterDFT ∷
  needTwistedCoordinateTauOddFunctionWeld ∷
  needCompleteCharacterBasisActionEquality ∷
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
    finalMagnitudeHypothesisMayCountAsItsOwnDerivation : Bool
    compiledMatrixEqualityShouldRemainOnSearchFrontier : Bool
    arbitraryUnitaryDFTMayCountAsOddCharacterDFT : Bool
    canonicalOrbitReceiptsShouldRemainOnSearchFrontier : Bool
    signedOrbitCancellationShouldRemainOnSearchFrontier : Bool
    explicitComplexPhaseValuesRequiredForMinusTwo : Bool

canonicalBidiFirewall : BidiFirewall
canonicalBidiFirewall =
  bidiFirewall false false false false false false false false false false

spatialSpectralCircleSingleSeamCutset :
  compileMissing (kind spectralCircleSpatialClaim)
  ≡ needInstantiateCorrectOddCharacterDFT ∷
    needTwistedCoordinateTauOddFunctionWeld ∷
    needCompleteCharacterBasisActionEquality ∷
    []
spatialSpectralCircleSingleSeamCutset = refl

spatialPowerSharesSameSeam :
  compileMissing (kind spatialTwistedPowerClaim)
  ≡ needInstantiateCorrectOddCharacterDFT ∷
    needTwistedCoordinateTauOddFunctionWeld ∷
    needCompleteCharacterBasisActionEquality ∷
    []
spatialPowerSharesSameSeam = refl

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
