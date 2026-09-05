module DASHI.Analysis.NonArchimedeanSpectralBidiObligationExact where

------------------------------------------------------------------------
-- Reverse / BIDI obligation compiler for the non-Archimedean spectral lane.
--
-- The finite spectral core is compiler-closed from checked source definitions
-- plus repo-owned Fourier, intertwiner, orbit, sign, determinant, and root-union
-- machinery.  The next live claim-strength question is the paper's separate
-- directed critical-sigma statement.
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
    "directed twisted-circle convergence has critical scaling exponent sigma=1/2"
    "independent definition of sigma + theorem connecting that definition to the radius sequence"
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
  needDirectedSigmaDefinition : MissingObligation
  needDirectedSigmaRadiusLinkTheorem : MissingObligation
  needGraphToDecompositionProducer : MissingObligation
  needDepthDecayProducer : MissingObligation
  needBoundaryEntropySameObjectWeld : MissingObligation
  needModelLevelRoPEConsumerTheorem : MissingObligation

compileMissing : ClaimKind → List MissingObligation
compileMissing spatialSpectralCircle = []
compileMissing spatialTwistedPower = []
compileMissing literalOneStepSpectrumUnion = []
compileMissing directedRadiusSigmaHalf =
  needDirectedSigmaDefinition ∷ needDirectedSigmaRadiusLinkTheorem ∷ []
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

directedSigmaExactCutset :
  compileMissing directedRadiusSigmaHalf
  ≡ needDirectedSigmaDefinition ∷ needDirectedSigmaRadiusLinkTheorem ∷ []
directedSigmaExactCutset = refl
