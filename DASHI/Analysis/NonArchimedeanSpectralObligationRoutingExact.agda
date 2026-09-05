module DASHI.Analysis.NonArchimedeanSpectralObligationRoutingExact where

------------------------------------------------------------------------
-- Typed claim-specific reverse routing.
--
-- After the finite-core reuse pass, the spatial spectral target has one
-- source-specific producer only: instantiate the concrete Lean ZMod-2 sheet
-- model in the owned DASHI binary-sheet/twisted-restriction adapter.  Character
-- labels, scalar action, period, orbit weight, signed return, and literal matrix
-- equality are now compiler output from existing source/repo owners.
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
  concreteSourceSheetAdapter : ProducerObligation
  graphToDecompositionConstruction : ProducerObligation
  activeSetDepthDecayBound : ProducerObligation
  entropySameObjectReceipt : ProducerObligation
  transformerLossOrFidelityTheorem : ProducerObligation

reverseRoute : SpectralTarget → List ProducerObligation
reverseRoute spatialSpectralCircle =
  concreteSourceSheetAdapter ∷ []
reverseRoute orbitProductInterpretation = []
reverseRoute arbitraryDagAdelicCover = graphToDecompositionConstruction ∷ []
reverseRoute depthDecaySparsity = activeSetDepthDecayBound ∷ []
reverseRoute contractedBoundaryEntropyLaw = entropySameObjectReceipt ∷ []
reverseRoute ropeModelOptimality = transformerLossOrFidelityTheorem ∷ []

spatialRouteExact :
  reverseRoute spatialSpectralCircle
  ≡ concreteSourceSheetAdapter ∷ []
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
