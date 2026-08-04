module DASHI.Physics.YangMills.BalabanP06CanonicalAnimalConstantExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Reinhard Diestel, "Graph Theory", Graduate Texts in Mathematics 173,
-- 5th edition, Springer, 2017. DOI: 10.1007/978-3-662-53622-3.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
--
-- The repository already proves the canonical mixed-reducer chain
--
--   bounded-degree size shells
--     + reduced-complexity/diameter control
--     + decoration multiplicity
--     + skeleton-decoration decomposition
--     -> rooted polymer animal count.
--
-- This module exposes the three actual constants produced by that chain.  It
-- does not ask a caller for a second animal-count theorem and it does not count
-- decorated polymers directly.  The only remaining physical input is the
-- existing P06ModelLeafDischargePackage.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; fst; snd)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)
open import Data.Nat.Base using (_≤_; _^_)

import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy
import DASHI.Physics.YangMills.GraphCombinatorics as Graph
open import DASHI.Physics.YangMills.CompactLieProofLevel

payloadFromModelLeaf :
  Entropy.P06ModelLeafDischargePackage →
  Entropy.BalabanP06MixedReducerPayload
payloadFromModelLeaf = Entropy.P06FromModelLeafDischargePackage

SkeletonCountingResult :
  Entropy.P06ModelLeafDischargePackage → Set₁
SkeletonCountingResult package =
  let payload = payloadFromModelLeaf package
      graphAdapter =
        Entropy.BalabanP06MixedReducerPayload.graphAdapter payload
      graph = Entropy.BalabanGraphAdapter.supportGraph graphAdapter
  in Σ Nat
       (λ C-skeleton →
         ∀ (root : Graph.Graph.Vertex graph) (diameter : Nat) →
         Graph.countReducedSkeletonsWithDiam graph root diameter
           ≤ C-skeleton ^ diameter)

DecorationCountingResult :
  Entropy.P06ModelLeafDischargePackage → Set₁
DecorationCountingResult package =
  let payload = payloadFromModelLeaf package
      graphAdapter =
        Entropy.BalabanP06MixedReducerPayload.graphAdapter payload
      graph = Entropy.BalabanGraphAdapter.supportGraph graphAdapter
      decorationAdapter =
        Entropy.BalabanP06MixedReducerPayload.decorationMultiplicityAdapter
          payload
      decoration =
        Entropy.BalabanDecorationMultiplicityAdapter.decorationMultiplicity
          decorationAdapter
  in Σ Nat
       (λ C-decoration →
         ∀ (root : Graph.Graph.Vertex graph)
           (vertices : List (Graph.Graph.Vertex graph))
           (reduced : Graph.RootedReducedSkeleton graph root vertices)
           (diameter : Nat) →
         Graph.diam_G {graph} vertices ≡ diameter →
         Graph.DecorationMultiplicity.countDecorations decoration vertices
           ≤ C-decoration ^ diameter)

AnimalCountingResult :
  Entropy.P06ModelLeafDischargePackage → Set₁
AnimalCountingResult package =
  let payload = payloadFromModelLeaf package
      graphAdapter =
        Entropy.BalabanP06MixedReducerPayload.graphAdapter payload
      graph = Entropy.BalabanGraphAdapter.supportGraph graphAdapter
  in Σ Nat
       (λ C-animal →
         ∀ (root : Graph.Graph.Vertex graph) (diameter : Nat) →
         Graph.countPolymersWithDiam graph root diameter
           ≤ C-animal ^ diameter)

canonicalSkeletonCounting :
  (package : Entropy.P06ModelLeafDischargePackage) →
  SkeletonCountingResult package
canonicalSkeletonCounting package =
  let payload = payloadFromModelLeaf package
      graphAdapter =
        Entropy.BalabanP06MixedReducerPayload.graphAdapter payload
      complexityAdapter =
        Entropy.BalabanP06MixedReducerPayload.reducedSkeletonComplexityAdapter
          payload
  in Entropy.BalabanCountingBoundReplacement
       graphAdapter
       complexityAdapter
       (Entropy.BalabanP06MixedReducerPayload.linearRangeSum payload)

canonicalDecorationCounting :
  (package : Entropy.P06ModelLeafDischargePackage) →
  DecorationCountingResult package
canonicalDecorationCounting package =
  let payload = payloadFromModelLeaf package
      graphAdapter =
        Entropy.BalabanP06MixedReducerPayload.graphAdapter payload
      complexityAdapter =
        Entropy.BalabanP06MixedReducerPayload.reducedSkeletonComplexityAdapter
          payload
      decorationAdapter =
        Entropy.BalabanP06MixedReducerPayload.decorationMultiplicityAdapter
          payload
  in Entropy.BalabanDecorationMultiplicityByDiameter
       graphAdapter complexityAdapter decorationAdapter

canonicalAnimalCounting :
  (package : Entropy.P06ModelLeafDischargePackage) →
  AnimalCountingResult package
canonicalAnimalCounting package =
  Entropy.BalabanP06AnimalCountingFromAdapters
    (payloadFromModelLeaf package)

record CanonicalP06AnimalConstantCertificate
    (package : Entropy.P06ModelLeafDischargePackage) : Set₁ where
  field
    skeletonCounting : SkeletonCountingResult package
    decorationCounting : DecorationCountingResult package
    animalCounting : AnimalCountingResult package

    skeletonCountingIsCanonical :
      skeletonCounting ≡ canonicalSkeletonCounting package

    decorationCountingIsCanonical :
      decorationCounting ≡ canonicalDecorationCounting package

    animalCountingIsCanonical :
      animalCounting ≡ canonicalAnimalCounting package

    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary ≡
      "P06 canonical constant certificate: the animal constant is produced by the owned reduced-skeleton/decoration mixed reducer from one physical P06 model-leaf package."

open CanonicalP06AnimalConstantCertificate public

canonicalP06AnimalConstantCertificate :
  (package : Entropy.P06ModelLeafDischargePackage) →
  CanonicalP06AnimalConstantCertificate package
canonicalP06AnimalConstantCertificate package = record
  { skeletonCounting = canonicalSkeletonCounting package
  ; decorationCounting = canonicalDecorationCounting package
  ; animalCounting = canonicalAnimalCounting package
  ; skeletonCountingIsCanonical = refl
  ; decorationCountingIsCanonical = refl
  ; animalCountingIsCanonical = refl
  ; proofBoundary =
      "P06 canonical constant certificate: the animal constant is produced by the owned reduced-skeleton/decoration mixed reducer from one physical P06 model-leaf package."
  ; proofBoundaryIsCanonical = refl
  }

canonicalSkeletonConstant :
  (package : Entropy.P06ModelLeafDischargePackage) → Nat
canonicalSkeletonConstant package =
  fst (canonicalSkeletonCounting package)

canonicalDecorationConstant :
  (package : Entropy.P06ModelLeafDischargePackage) → Nat
canonicalDecorationConstant package =
  fst (canonicalDecorationCounting package)

canonicalAnimalConstant :
  (package : Entropy.P06ModelLeafDischargePackage) → Nat
canonicalAnimalConstant package =
  fst (canonicalAnimalCounting package)

canonicalAnimalCountBound :
  (package : Entropy.P06ModelLeafDischargePackage) →
  let payload = payloadFromModelLeaf package
      graphAdapter =
        Entropy.BalabanP06MixedReducerPayload.graphAdapter payload
      graph = Entropy.BalabanGraphAdapter.supportGraph graphAdapter
  in ∀ (root : Graph.Graph.Vertex graph) (diameter : Nat) →
       Graph.countPolymersWithDiam graph root diameter
         ≤ canonicalAnimalConstant package ^ diameter
canonicalAnimalCountBound package =
  snd (canonicalAnimalCounting package)

p06CanonicalAnimalConstantLevel : ProofLevel
p06CanonicalAnimalConstantLevel = machineChecked

p06PhysicalModelLeafInputsLevel : ProofLevel
p06PhysicalModelLeafInputsLevel = conditional
