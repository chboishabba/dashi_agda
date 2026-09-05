module DASHI.Analysis.NonArchimedeanSpectralBidiObligationExact where

------------------------------------------------------------------------
-- Reverse / BIDI obligation compiler for the non-Archimedean spectral lane.
--
-- The finite spectral core is compiler-closed.  The post-closure audit now
-- separates three distinct half-valued objects:
--
--   * directed radius level-contraction factor 1/2;
--   * cyclotomic amplitude exponent sigma_cyc = log_2 |W_C| = 1/2;
--   * Prolate/Archimedean critical-line parameter sigma = 1/2.
--
-- The local p=2 anchor is repaired using the primitive twisted-circle radius
-- r_tw(2)=sqrt 2, not a full transfer-operator spectral radius.  That local
-- half-value is now compiler-closed.  The only remaining anchor obligation is
-- a same-object compatibility theorem between the local cyclotomic sigma and
-- the independent Prolate sigma parameter.
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
spectralCircleSpatialClaim =
  bidiClaim spatialSpectralCircle
    "spatial twisted-block spectral circle"
    "compiler-closed from concrete sheet definitions + corrected odd-character weld"
    true

spatialTwistedPowerClaim : BidiClaim
spatialTwistedPowerClaim =
  bidiClaim spatialTwistedPower
    "spatial twisted-block doubled-return power equals minus two identity"
    "same compiler-closed spatial weld + owned signed-return arithmetic"
    true

spectrumTowerClaim : BidiClaim
spectrumTowerClaim =
  bidiClaim literalOneStepSpectrumUnion
    "literal one-step spectrum union"
    "characteristic determinant factorization + characteristic root union compiler"
    true

directedSigmaClaim : BidiClaim
directedSigmaClaim =
  bidiClaim directedRadiusSigmaHalf
    "directed twisted-circle radius convergence itself has size exponent sigma=1/2"
    "independent definition of radius sigma + theorem connecting it to the N=2^n scaling law"
    false

cyclotomicSigmaClaim : BidiClaim
cyclotomicSigmaClaim =
  bidiClaim cyclotomicSigmaHalf
    "cyclotomic local amplitude exponent sigma_cyc = log_2 r_tw(2) equals 1/2"
    "source r_tw(2)=sqrt two + source log2_sqrt_two theorem"
    true

prolateSigmaClaim : BidiClaim
prolateSigmaClaim =
  bidiClaim prolateCriticalLineHalf
    "Prolate/Archimedean critical-line parameter has distinguished value sigma=1/2"
    "ProlateScaling secular-imaginary and normal-gap theorems"
    true

sigmaAnchorClaim : BidiClaim
sigmaAnchorClaim =
  bidiClaim cyclotomicAnchorsProlateHalf
    "cyclotomic sigma_cyc=1/2 algebraically anchors the Prolate critical-line sigma=1/2"
    "two-sided sigma same-object weld preserving anchor and critical conditions"
    false

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
compileMissing orbitProduct = []
compileMissing arbitraryDagCover = needGraphToDecompositionProducer ∷ []
compileMissing depthDecaySparsity = needDepthDecayProducer ∷ []
compileMissing contractedBoundaryEntropy = needBoundaryEntropySameObjectWeld ∷ []
compileMissing ropeOptimality = needModelLevelRoPEConsumerTheorem ∷ []

finiteSpatialCoreClosed :
  compileMissing spatialSpectralCircle ≡ []
finiteSpatialCoreClosed = refl

finitePowerCoreClosed :
  compileMissing spatialTwistedPower ≡ []
finitePowerCoreClosed = refl

spectrumTowerRepoClosed :
  compileMissing literalOneStepSpectrumUnion ≡ []
spectrumTowerRepoClosed = refl

cyclotomicSigmaHalfClosed :
  compileMissing cyclotomicSigmaHalf ≡ []
cyclotomicSigmaHalfClosed = refl

prolateCriticalLineHalfClosed :
  compileMissing prolateCriticalLineHalf ≡ []
prolateCriticalLineHalfClosed = refl

directedRadiusSigmaExactCutset :
  compileMissing directedRadiusSigmaHalf
  ≡ needDirectedRadiusSigmaDefinition ∷ needDirectedRadiusSigmaScalingTheorem ∷ []
directedRadiusSigmaExactCutset = refl

sigmaAnchorSingleWeldCutset :
  compileMissing cyclotomicAnchorsProlateHalf
  ≡ needCyclotomicToProlateSigmaSameObjectWeld ∷ []
sigmaAnchorSingleWeldCutset = refl
