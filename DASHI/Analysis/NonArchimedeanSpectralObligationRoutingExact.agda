module DASHI.Analysis.NonArchimedeanSpectralObligationRoutingExact where

------------------------------------------------------------------------
-- Typed claim-specific reverse routing.
--
-- This avoids string-dispatch entirely.  Targets route to a list of exact
-- producer obligations so a multi-coordinate cutset is not collapsed into one
-- generic missing-proof label.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data SpectralTarget : Set where
  spatialSpectralCircle : SpectralTarget
  orbitProductInterpretation : SpectralTarget
  arbitraryDagAdelicCover : SpectralTarget
  depthDecaySparsity : SpectralTarget
  contractedBoundaryEntropyLaw : SpectralTarget
  ropeModelOptimality : SpectralTarget


data ProducerObligation : Set where
  concreteTwistedCharacterRechart : ProducerObligation
  concreteGroupLabelling : ProducerObligation
  concreteScalarActionWeld : ProducerObligation
  concretePeriodAttachment : ProducerObligation
  concreteOrbitWeightAttachment : ProducerObligation
  orbitPartitionReceipt : ProducerObligation
  graphToDecompositionConstruction : ProducerObligation
  activeSetDepthDecayBound : ProducerObligation
  entropySameObjectReceipt : ProducerObligation
  transformerLossOrFidelityTheorem : ProducerObligation

reverseRoute : SpectralTarget → List ProducerObligation
reverseRoute spatialSpectralCircle =
  concreteTwistedCharacterRechart ∷
  concreteGroupLabelling ∷
  concreteScalarActionWeld ∷
  concretePeriodAttachment ∷
  concreteOrbitWeightAttachment ∷
  []
reverseRoute orbitProductInterpretation = []
reverseRoute arbitraryDagAdelicCover = graphToDecompositionConstruction ∷ []
reverseRoute depthDecaySparsity = activeSetDepthDecayBound ∷ []
reverseRoute contractedBoundaryEntropyLaw = entropySameObjectReceipt ∷ []
reverseRoute ropeModelOptimality = transformerLossOrFidelityTheorem ∷ []

spatialRouteExact :
  reverseRoute spatialSpectralCircle
  ≡ concreteTwistedCharacterRechart ∷
    concreteGroupLabelling ∷
    concreteScalarActionWeld ∷
    concretePeriodAttachment ∷
    concreteOrbitWeightAttachment ∷
    []
spatialRouteExact = refl

orbitProductRouteExact :
  reverseRoute orbitProductInterpretation ≡ []
orbitProductRouteExact = refl

multiPrimeCoverRouteExact :
  reverseRoute arbitraryDagAdelicCover
  ≡ graphToDecompositionConstruction ∷ []
multiPrimeCoverRouteExact = refl

sparsityRouteExact :
  reverseRoute depthDecaySparsity ≡ activeSetDepthDecayBound ∷ []
sparsityRouteExact = refl

entropyRouteExact :
  reverseRoute contractedBoundaryEntropyLaw ≡ entropySameObjectReceipt ∷ []
entropyRouteExact = refl

ropeRouteExact :
  reverseRoute ropeModelOptimality ≡ transformerLossOrFidelityTheorem ∷ []
ropeRouteExact = refl
