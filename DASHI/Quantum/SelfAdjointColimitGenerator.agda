module DASHI.Quantum.SelfAdjointColimitGenerator where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Unifier using (HilbertSpace)
open import DASHI.Quantum.DepthEmbeddingIsometry using (DepthCarrier)
open import DASHI.Quantum.GNSUniversalProperty using
  (GNSUniversalPropertyWitness; canonicalGNSUniversalPropertyWitness)
open import DASHI.Quantum.Stone using
  (FiniteDepthIdentityStoneTowerSkeleton;
   FinitelySupportedDepthColimitDomain; StoneSelfAdjoint;
   onePointDiscreteIdentityDepthSystem;
   onePointFiniteDepthIdentityStoneTowerSkeleton; onePointFiniteHamiltonian;
   onePointFiniteHamiltonianSelfAdjoint; onePointFiniteHilbertSpace;
   onePointFiniteSelfAdjointHamiltonianStoneData;
   onePointFiniteSupportColimitDomain)

-- The depth-0 carrier of the finite tower is the one-point Hilbert space.
-- The colimit generator is therefore the concrete one-point Hamiltonian.

ColimitHilbert : HilbertSpace
ColimitHilbert = onePointFiniteHilbertSpace

ColimitVector : Set
ColimitVector = DepthCarrier zero

H : ColimitVector → ColimitVector
H = onePointFiniteHamiltonian

H-is-canonical :
  (x : ColimitVector) →
  H x ≡ onePointFiniteHamiltonian x
H-is-canonical _ = refl

colimitGeneratorSelfAdjoint :
  StoneSelfAdjoint ColimitHilbert H
colimitGeneratorSelfAdjoint = onePointFiniteHamiltonianSelfAdjoint

finiteSupportColimitDomain :
  FinitelySupportedDepthColimitDomain onePointDiscreteIdentityDepthSystem
finiteSupportColimitDomain = onePointFiniteSupportColimitDomain

record SelfAdjointColimitGeneratorWitness : Setω where
  field
    gnsUniversalProperty :
      GNSUniversalPropertyWitness

    depthSkeleton :
      FiniteDepthIdentityStoneTowerSkeleton

    depthSkeletonIsCanonical :
      depthSkeleton ≡ onePointFiniteDepthIdentityStoneTowerSkeleton

    finiteSupportDomain :
      FinitelySupportedDepthColimitDomain onePointDiscreteIdentityDepthSystem

    finiteSupportDomainIsCanonical :
      finiteSupportDomain ≡ finiteSupportColimitDomain

    generator :
      ColimitVector → ColimitVector

    generatorIsCanonical :
      (x : ColimitVector) → generator x ≡ H x

    generatorSelfAdjoint :
      StoneSelfAdjoint ColimitHilbert generator

    generatorSelfAdjointIsCanonical :
      generatorSelfAdjoint ≡ colimitGeneratorSelfAdjoint

    witnessBoundary :
      List String

open SelfAdjointColimitGeneratorWitness public

canonicalSelfAdjointColimitGeneratorWitness :
  SelfAdjointColimitGeneratorWitness
canonicalSelfAdjointColimitGeneratorWitness =
  record
    { gnsUniversalProperty = canonicalGNSUniversalPropertyWitness
    ; depthSkeleton = onePointFiniteDepthIdentityStoneTowerSkeleton
    ; depthSkeletonIsCanonical = refl
    ; finiteSupportDomain = onePointFiniteSupportColimitDomain
    ; finiteSupportDomainIsCanonical = refl
    ; generator = H
    ; generatorIsCanonical = H-is-canonical
    ; generatorSelfAdjoint = colimitGeneratorSelfAdjoint
    ; generatorSelfAdjointIsCanonical = refl
    ; witnessBoundary =
        "SelfAdjointColimitGenerator packages the concrete one-point Stone Hamiltonian"
        ∷ "The finite-support depth skeleton is the inhabited Stone witness"
        ∷ "The depth-0 colimit vector is the one-point carrier from Stone"
        ∷ "Self-adjointness is inherited from onePointFiniteHamiltonianSelfAdjoint"
        ∷ []
    }

selfAdjointColimitGeneratorBoundary : List String
selfAdjointColimitGeneratorBoundary =
  "SelfAdjointColimitGenerator is concrete and finite: the generator is the Stone one-point Hamiltonian"
  ∷ "The finite-support colimit domain is the existing Stone witness"
  ∷ []
