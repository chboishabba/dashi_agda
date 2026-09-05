module DASHI.Analysis.NonArchimedeanSpectralObligationRoutingExact where

------------------------------------------------------------------------
-- Typed claim-specific reverse routing.
--
-- The finite spectral core is closed in the current DASHI compiler graph.
-- The next source-strength question is the paper's directed sigma=1/2 claim.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data SpectralTarget : Set where
  spatialSpectralCircle : SpectralTarget
  spatialTwistedPower : SpectralTarget
  literalOneStepSpectrumUnion : SpectralTarget
  directedRadiusSigmaHalf : SpectralTarget
  orbitProductInterpretation : SpectralTarget
  arbitraryDagAdelicCover : SpectralTarget
  depthDecaySparsity : SpectralTarget
  contractedBoundaryEntropyLaw : SpectralTarget
  ropeModelOptimality : SpectralTarget


data ProducerObligation : Set where
  defineDirectedSigma : ProducerObligation
  proveDirectedSigmaRadiusLink : ProducerObligation
  graphToDecompositionConstruction : ProducerObligation
  activeSetDepthDecayBound : ProducerObligation
  entropySameObjectReceipt : ProducerObligation
  transformerLossOrFidelityTheorem : ProducerObligation

reverseRoute : SpectralTarget → List ProducerObligation
reverseRoute spatialSpectralCircle = []
reverseRoute spatialTwistedPower = []
reverseRoute literalOneStepSpectrumUnion = []
reverseRoute directedRadiusSigmaHalf =
  defineDirectedSigma ∷ proveDirectedSigmaRadiusLink ∷ []
reverseRoute orbitProductInterpretation = []
reverseRoute arbitraryDagAdelicCover = graphToDecompositionConstruction ∷ []
reverseRoute depthDecaySparsity = activeSetDepthDecayBound ∷ []
reverseRoute contractedBoundaryEntropyLaw = entropySameObjectReceipt ∷ []
reverseRoute ropeModelOptimality = transformerLossOrFidelityTheorem ∷ []

finiteCircleClosed : reverseRoute spatialSpectralCircle ≡ []
finiteCircleClosed = refl

finitePowerClosed : reverseRoute spatialTwistedPower ≡ []
finitePowerClosed = refl

towerClosed : reverseRoute literalOneStepSpectrumUnion ≡ []
towerClosed = refl

directedSigmaRouteExact :
  reverseRoute directedRadiusSigmaHalf
  ≡ defineDirectedSigma ∷ proveDirectedSigmaRadiusLink ∷ []
directedSigmaRouteExact = refl
