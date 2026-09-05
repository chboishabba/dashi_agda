module DASHI.Analysis.NonArchimedeanSpectralBidiObligationExact where

------------------------------------------------------------------------
-- Reverse / BIDI obligation compiler for the non-Archimedean spectral lane.
--
-- Finite spectral closure is dependency-closed.  Post-closure continuous and
-- Markov claims are routed at their actual theorem strength.  In particular,
-- the source's unit-prefactor one-step L2 contraction is refuted at n=3; the
-- viable replacement is a level-dependent prefactored power bound assembled
-- from the monomial shell powers through the unitary Fourier energy chart.
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
  "independent definition of radius sigma + theorem connecting it to N=2^n scaling" false

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
  "cyclotomic sigma_cyc=1/2 algebraically anchors the Prolate critical-line sigma=1/2"
  "two-sided sigma same-object weld preserving anchor and critical conditions" false

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
  "explicit shell prefactor + Parseval shell-energy same-object weld" false

totalVariationClaim : BidiClaim
totalVariationClaim = bidiClaim totalVariationMixing
  "finite walk has total-variation mixing from repaired prefactored L2 decay"
  "prefactored L2 power bound + finite Cauchy-Schwarz consumer" false

correlationDecayClaim : BidiClaim
correlationDecayClaim = bidiClaim correlationDecayAtInverseSqrtTwo
  "correlations decay at inverse-sqrt-two spectral rate with a finite prefactor"
  "prefactored L2 mixing + correlation consumer identification" false

stoppingSurvivalClaim : BidiClaim
stoppingSurvivalClaim = bidiClaim universalStoppingSurvivalBound
  "every nontrivial stopping set has survival tail C 2^(-t/2)"
  "independent killed/substochastic-kernel power bound" false

stoppingMomentsClaim : BidiClaim
stoppingMomentsClaim = bidiClaim stoppingMomentFiniteness
  "all stopping-time moments follow from the inverse-sqrt-two survival tail"
  "valid survival-tail producer + generating-function consumer" false

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
  needDirectedRadiusSigmaDefinition : MissingObligation
  needDirectedRadiusSigmaScalingTheorem : MissingObligation
  needCyclotomicToProlateSigmaSameObjectWeld : MissingObligation
  needGibbsUniquenessTheorem : MissingObligation

  rejectedUnitPrefactorOneStepContraction : MissingObligation
  needInputParsevalShellEnergyWeld : MissingObligation
  needOutputParsevalShellEnergyWeld : MissingObligation
  needCorrelationConsumerWeld : MissingObligation
  needKilledKernelPowerBound : MissingObligation
  needStoppingTailGeneratingFunctionConsumer : MissingObligation
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
compileMissing directedRadiusSigmaHalf =
  needDirectedRadiusSigmaDefinition ∷ needDirectedRadiusSigmaScalingTheorem ∷ []
compileMissing cyclotomicSigmaHalf = []
compileMissing prolateCriticalLineHalf = []
compileMissing cyclotomicAnchorsProlateHalf =
  needCyclotomicToProlateSigmaSameObjectWeld ∷ []
compileMissing uniqueHaarConformalGibbs = needGibbsUniquenessTheorem ∷ []

compileMissing unitPrefactorOneStepL2Contraction =
  rejectedUnitPrefactorOneStepContraction ∷ []
compileMissing prefactoredL2PowerMixing =
  needInputParsevalShellEnergyWeld ∷
  needOutputParsevalShellEnergyWeld ∷ []
compileMissing totalVariationMixing =
  needInputParsevalShellEnergyWeld ∷
  needOutputParsevalShellEnergyWeld ∷ []
compileMissing correlationDecayAtInverseSqrtTwo =
  needInputParsevalShellEnergyWeld ∷
  needOutputParsevalShellEnergyWeld ∷
  needCorrelationConsumerWeld ∷ []
compileMissing universalStoppingSurvivalBound =
  needKilledKernelPowerBound ∷ []
compileMissing stoppingMomentFiniteness =
  needKilledKernelPowerBound ∷
  needStoppingTailGeneratingFunctionConsumer ∷ []
compileMissing taoStyleStoppingConcentration =
  needMarkovConcentrationHypotheses ∷
  needDriftStoppingSameObjectWeld ∷ []

compileMissing fullContinuousTransferRadiusSqrtTwo =
  rejectedFullTransferRadiusSqrtTwo ∷ []
compileMissing orbitProduct = []
compileMissing arbitraryDagCover = needGraphToDecompositionProducer ∷ []
compileMissing depthDecaySparsity = needDepthDecayProducer ∷ []
compileMissing contractedBoundaryEntropy = needBoundaryEntropySameObjectWeld ∷ []
compileMissing ropeOptimality = needModelLevelRoPEConsumerTheorem ∷ []

finiteSpatialCoreClosed : compileMissing spatialSpectralCircle ≡ []
finiteSpatialCoreClosed = refl

spectrumTowerRepoClosed : compileMissing literalOneStepSpectrumUnion ≡ []
spectrumTowerRepoClosed = refl

sigmaAnchorSingleWeldCutset :
  compileMissing cyclotomicAnchorsProlateHalf
  ≡ needCyclotomicToProlateSigmaSameObjectWeld ∷ []
sigmaAnchorSingleWeldCutset = refl

gibbsUniquenessExactCutset :
  compileMissing uniqueHaarConformalGibbs ≡ needGibbsUniquenessTheorem ∷ []
gibbsUniquenessExactCutset = refl

unitOneStepContractionRejected :
  compileMissing unitPrefactorOneStepL2Contraction
  ≡ rejectedUnitPrefactorOneStepContraction ∷ []
unitOneStepContractionRejected = refl

prefactoredMixingExactCutset :
  compileMissing prefactoredL2PowerMixing
  ≡ needInputParsevalShellEnergyWeld ∷
    needOutputParsevalShellEnergyWeld ∷ []
prefactoredMixingExactCutset = refl

stoppingSurvivalNeedsIndependentProducer :
  compileMissing universalStoppingSurvivalBound
  ≡ needKilledKernelPowerBound ∷ []
stoppingSurvivalNeedsIndependentProducer = refl

fullTransferSqrtTwoRejected :
  compileMissing fullContinuousTransferRadiusSqrtTwo
  ≡ rejectedFullTransferRadiusSqrtTwo ∷ []
fullTransferSqrtTwoRejected = refl
