module DASHI.Analysis.NonArchimedeanSpectralObligationRoutingExact where

------------------------------------------------------------------------
-- Typed claim-specific reverse routing.
--
-- This avoids string-dispatch entirely: each downstream target is a distinct
-- constructor, so reverse proof search cannot accidentally merge obligations
-- merely because they share the same Boolean status summary.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)


data SpectralTarget : Set where
  spatialSpectralCircle : SpectralTarget
  orbitProductInterpretation : SpectralTarget
  arbitraryDagAdelicCover : SpectralTarget
  depthDecaySparsity : SpectralTarget
  contractedBoundaryEntropyLaw : SpectralTarget
  ropeModelOptimality : SpectralTarget


data ProducerObligation : Set where
  explicitFourierIntertwiner : ProducerObligation
  orbitPartitionReceipt : ProducerObligation
  graphToDecompositionConstruction : ProducerObligation
  activeSetDepthDecayBound : ProducerObligation
  entropySameObjectReceipt : ProducerObligation
  transformerLossOrFidelityTheorem : ProducerObligation
  alreadyOwned : ProducerObligation

reverseRoute : SpectralTarget → ProducerObligation
reverseRoute spatialSpectralCircle = explicitFourierIntertwiner
reverseRoute orbitProductInterpretation = alreadyOwned
reverseRoute arbitraryDagAdelicCover = graphToDecompositionConstruction
reverseRoute depthDecaySparsity = activeSetDepthDecayBound
reverseRoute contractedBoundaryEntropyLaw = entropySameObjectReceipt
reverseRoute ropeModelOptimality = transformerLossOrFidelityTheorem

spatialRouteExact :
  reverseRoute spatialSpectralCircle ≡ explicitFourierIntertwiner
spatialRouteExact = refl

orbitProductRouteExact :
  reverseRoute orbitProductInterpretation ≡ alreadyOwned
orbitProductRouteExact = refl

multiPrimeCoverRouteExact :
  reverseRoute arbitraryDagAdelicCover ≡ graphToDecompositionConstruction
multiPrimeCoverRouteExact = refl

sparsityRouteExact :
  reverseRoute depthDecaySparsity ≡ activeSetDepthDecayBound
sparsityRouteExact = refl

entropyRouteExact :
  reverseRoute contractedBoundaryEntropyLaw ≡ entropySameObjectReceipt
entropyRouteExact = refl

ropeRouteExact :
  reverseRoute ropeModelOptimality ≡ transformerLossOrFidelityTheorem
ropeRouteExact = refl
