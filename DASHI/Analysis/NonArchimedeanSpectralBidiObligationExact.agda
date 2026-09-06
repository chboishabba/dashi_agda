module DASHI.Analysis.NonArchimedeanSpectralBidiObligationExact where

------------------------------------------------------------------------
-- Reverse / BIDI obligation compiler for the non-Archimedean spectral lane.
--
-- Finite spectral closure is dependency-closed. Post-closure continuous and
-- Markov claims are routed at their actual theorem strength.
--
-- Closed-positive repaired lanes:
--   * finite C_n-prefactored L2 power mixing;
--   * Hilbert and normalized stationary covariance decay;
--   * total variation after adjoint orientation and finite L1/L2 welds;
--   * constructive set-dependent geometric stopping tails;
--   * all polynomial stopping moments and repaired block-dependent MGF strip.
--
-- Closed-negative advertised lanes:
--   * unit-prefactor one-step L2 inverse-sqrt-two contraction;
--   * universal sqrt(|A^c|) 2^(-t/2) stopping-survival bound;
--   * universal Re(s)<(1/2)log 2 stopping MGF strip;
--   * cyclotomic/2-adic factor alone anchors the Prolate critical sigma.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)


data ClaimKind : Set where
  spatialSpectralCircle : ClaimKind
  spatialTwistedPower : ClaimKind
  literalOneStepSpectrumUnion : ClaimKind
  directedRadiusSigmaHalf : ClaimKind
  cyclotomicSigmaHalf : ClaimKind
  prolateCriticalLineHalf : ClaimKind
  cyclotomicAnchorsProlateHalf : ClaimKind
  uniqueHaarConformalGibbs : ClaimKind
  unitPrefactorOneStepL2Contraction : ClaimKind
  prefactoredL2PowerMixing : ClaimKind
  totalVariationMixing : ClaimKind
  correlationDecayAtInverseSqrtTwo : ClaimKind
  universalStoppingSurvivalBound : ClaimKind
  setDependentStoppingSurvivalBound : ClaimKind
  stoppingMomentFiniteness : ClaimKind
  taoStyleStoppingConcentration : ClaimKind
  fullContinuousTransferRadiusSqrtTwo : ClaimKind
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
    promotionAllowed : Bool

open BidiClaim public

spectralCircleSpatialClaim : BidiClaim
spectralCircleSpatialClaim = bidiClaim spatialSpectralCircle
  "spatial twisted-block spectral circle"
  "compiler-closed from concrete sheet definitions + corrected odd-character weld" true

spatialTwistedPowerClaim : BidiClaim
spatialTwistedPowerClaim = bidiClaim spatialTwistedPower
  "spatial twisted-block doubled-return power equals minus two identity"
  "same compiler-closed spatial weld + owned signed-return arithmetic" true

spectrumTowerClaim : BidiClaim
spectrumTowerClaim = bidiClaim literalOneStepSpectrumUnion
  "literal one-step spectrum union"
  "characteristic determinant factorization + characteristic root union compiler" true

directedSigmaClaim : BidiClaim
directedSigmaClaim = bidiClaim directedRadiusSigmaHalf
  "directed twisted-circle radius convergence itself has size exponent sigma=1/2"
  "rejected N-scaling reading: log radius is proportional to N^-1" false

cyclotomicSigmaClaim : BidiClaim
cyclotomicSigmaClaim = bidiClaim cyclotomicSigmaHalf
  "cyclotomic local amplitude exponent sigma_cyc = log_2 r_tw(2) equals 1/2"
  "source r_tw(2)=sqrt two + source log2_sqrt_two theorem" true

prolateSigmaClaim : BidiClaim
prolateSigmaClaim = bidiClaim prolateCriticalLineHalf
  "Prolate/Archimedean critical-line parameter has distinguished value sigma=1/2"
  "ProlateScaling secular-imaginary and normal-gap theorems" true

sigmaAnchorClaim : BidiClaim
sigmaAnchorClaim = bidiClaim cyclotomicAnchorsProlateHalf
  "cyclotomic sigma_cyc=1/2 algebraically determines the Prolate critical-line sigma=1/2"
  "rejected by semilocal sigma non-factorability at fixed 2-adic factor" false

gibbsUniquenessClaim : BidiClaim
gibbsUniquenessClaim = bidiClaim uniqueHaarConformalGibbs
  "normalized Haar is the unique conformal Gibbs state"
  "dedicated Gibbs uniqueness/ergodicity producer" false

unitOneStepClaim : BidiClaim
unitOneStepClaim = bidiClaim unitPrefactorOneStepL2Contraction
  "every mean-zero state contracts by 1/sqrt two in one step"
  "rejected by exact n=3 rational counterexample" false

prefactoredMixingClaim : BidiClaim
prefactoredMixingClaim = bidiClaim prefactoredL2PowerMixing
  "finite normalized walk has C_n-prefactored inverse-sqrt-two L2 power decay"
  "Euclidean L2 weld + corrected Hadamard energy tower + unitary DFT + finite shell maximum" true

totalVariationClaim : BidiClaim
totalVariationClaim = bidiClaim totalVariationMixing
  "finite walk has total-variation mixing from repaired prefactored L2 decay"
  "adjoint-power norm weld + density coordinate identity + finite L1/L2 consumer" true

correlationDecayClaim : BidiClaim
correlationDecayClaim = bidiClaim correlationDecayAtInverseSqrtTwo
  "Hilbert and uniform-stationary covariance correlations decay at inverse-sqrt-two rate with finite prefactor"
  "prefactored L2 mixing + uniform stationarity + inverse-state-count covariance normalization" true

universalStoppingSurvivalClaim : BidiClaim
universalStoppingSurvivalClaim = bidiClaim universalStoppingSurvivalBound
  "every nontrivial stopping set has tail sqrt(|A^c|) 2^(-t/2)"
  "rejected by exact n=3 A={4}, x0=1, t=3 counterexample" false

setDependentStoppingSurvivalClaim : BidiClaim
setDependentStoppingSurvivalClaim = bidiClaim setDependentStoppingSurvivalBound
  "each fixed finite stopping set has some set-dependent exponential survival tail"
  "forward translation + finite witness maximum + prefix absorption + generic finite branching tail compiler" true

stoppingMomentsClaim : BidiClaim
stoppingMomentsClaim = bidiClaim stoppingMomentFiniteness
  "all polynomial stopping moments are finite under the repaired set-dependent geometric tail"
  "Mathlib summable_pow_mul_exp_neg_nat_mul + repaired positive block rate" true

taoConcentrationClaim : BidiClaim
taoConcentrationClaim = bidiClaim taoStyleStoppingConcentration
  "Tao-style logarithmic stopping concentration follows from the finite spectral gap"
  "separate Markov concentration hypotheses + same-object drift/stopping weld" false

fullTransferRadiusClaim : BidiClaim
fullTransferRadiusClaim = bidiClaim fullContinuousTransferRadiusSqrtTwo
  "full unnormalised continuous transfer operator has spectral radius sqrt two"
  "rejected object interpretation: source owns constant eigenvalue two" false

orbitProductClaim : BidiClaim
orbitProductClaim = bidiClaim orbitProduct
  "two x3 orbit products multiply to two"
  "odd-residue cyclotomic product + compiled canonical partition" true

multiPrimeCoverClaim : BidiClaim
multiPrimeCoverClaim = bidiClaim arbitraryDagCover
  "arbitrary DAG admits multi-prime adelic cover"
  "construction of MultiPrimeTreeDecomposition from graph hypotheses" false

multiPrimeSparsityClaim : BidiClaim
multiPrimeSparsityClaim = bidiClaim depthDecaySparsity
  "depth-decaying active attention fraction"
  "quantitative depth-to-active-set bound" false

holographicAreaClaim : BidiClaim
holographicAreaClaim = bidiClaim contractedBoundaryEntropy
  "contracted boundary-state entropy equals cut size times log two"
  "same-object contracted-density entropy weld" false

ropeOptimalityClaim : BidiClaim
ropeOptimalityClaim = bidiClaim ropeOptimality
  "RoPE medoid compression is transformer-optimal"
  "model-level loss/fidelity theorem" false


data MissingObligation : Set where
  rejectedDirectedRadiusSizeExponentHalf : MissingObligation
  rejectedCurrentSemilocalSigmaAnchor : MissingObligation
  needGibbsUniquenessTheorem : MissingObligation
  rejectedUnitPrefactorOneStepContraction : MissingObligation
  rejectedUniversalStoppingSurvivalBound : MissingObligation
  rejectedUniversalHalfLogTwoMGFDomain : MissingObligation
  needMarkovConcentrationHypotheses : MissingObligation
  needDriftStoppingSameObjectWeld : MissingObligation
  rejectedFullTransferRadiusSqrtTwo : MissingObligation
  needGraphToDecompositionProducer : MissingObligation
  needDepthDecayProducer : MissingObligation
  needBoundaryEntropySameObjectWeld : MissingObligation
  needModelLevelRoPEConsumerTheorem : MissingObligation

compileMissing : ClaimKind → List MissingObligation
compileMissing spatialSpectralCircle = []
compileMissing spatialTwistedPower = []
compileMissing literalOneStepSpectrumUnion = []
compileMissing directedRadiusSigmaHalf = rejectedDirectedRadiusSizeExponentHalf ∷ []
compileMissing cyclotomicSigmaHalf = []
compileMissing prolateCriticalLineHalf = []
compileMissing cyclotomicAnchorsProlateHalf = rejectedCurrentSemilocalSigmaAnchor ∷ []
compileMissing uniqueHaarConformalGibbs = needGibbsUniquenessTheorem ∷ []
compileMissing unitPrefactorOneStepL2Contraction = rejectedUnitPrefactorOneStepContraction ∷ []
compileMissing prefactoredL2PowerMixing = []
compileMissing totalVariationMixing = []
compileMissing correlationDecayAtInverseSqrtTwo = []
compileMissing universalStoppingSurvivalBound = rejectedUniversalStoppingSurvivalBound ∷ []
compileMissing setDependentStoppingSurvivalBound = []
compileMissing stoppingMomentFiniteness = []
compileMissing taoStyleStoppingConcentration =
  needMarkovConcentrationHypotheses ∷ needDriftStoppingSameObjectWeld ∷ []
compileMissing fullContinuousTransferRadiusSqrtTwo = rejectedFullTransferRadiusSqrtTwo ∷ []
compileMissing orbitProduct = []
compileMissing arbitraryDagCover = needGraphToDecompositionProducer ∷ []
compileMissing depthDecaySparsity = needDepthDecayProducer ∷ []
compileMissing contractedBoundaryEntropy = needBoundaryEntropySameObjectWeld ∷ []
compileMissing ropeOptimality = needModelLevelRoPEConsumerTheorem ∷ []

finiteSpatialCoreClosed : compileMissing spatialSpectralCircle ≡ []
finiteSpatialCoreClosed = refl

spectrumTowerRepoClosed : compileMissing literalOneStepSpectrumUnion ≡ []
spectrumTowerRepoClosed = refl

sigmaAnchorClosedNegative :
  compileMissing cyclotomicAnchorsProlateHalf
  ≡ rejectedCurrentSemilocalSigmaAnchor ∷ []
sigmaAnchorClosedNegative = refl

gibbsUniquenessExactCutset :
  compileMissing uniqueHaarConformalGibbs ≡ needGibbsUniquenessTheorem ∷ []
gibbsUniquenessExactCutset = refl

unitOneStepContractionRejected :
  compileMissing unitPrefactorOneStepL2Contraction
  ≡ rejectedUnitPrefactorOneStepContraction ∷ []
unitOneStepContractionRejected = refl

prefactoredMixingClosed : compileMissing prefactoredL2PowerMixing ≡ []
prefactoredMixingClosed = refl

totalVariationMixingClosed : compileMissing totalVariationMixing ≡ []
totalVariationMixingClosed = refl

stationaryCorrelationDecayClosed :
  compileMissing correlationDecayAtInverseSqrtTwo ≡ []
stationaryCorrelationDecayClosed = refl

universalStoppingSurvivalRejected :
  compileMissing universalStoppingSurvivalBound
  ≡ rejectedUniversalStoppingSurvivalBound ∷ []
universalStoppingSurvivalRejected = refl

constructiveSetDependentStoppingTailClosed :
  compileMissing setDependentStoppingSurvivalBound ≡ []
constructiveSetDependentStoppingTailClosed = refl

stoppingMomentsClosed : compileMissing stoppingMomentFiniteness ≡ []
stoppingMomentsClosed = refl

fullTransferSqrtTwoRejected :
  compileMissing fullContinuousTransferRadiusSqrtTwo
  ≡ rejectedFullTransferRadiusSqrtTwo ∷ []
fullTransferSqrtTwoRejected = refl
