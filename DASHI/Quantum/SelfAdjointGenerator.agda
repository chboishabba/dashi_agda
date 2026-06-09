module DASHI.Quantum.SelfAdjointGenerator where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Unifier using (ℝ; toℝ; HilbertSpace)
open import DASHI.Quantum.DepthEmbeddingIsometry using (DepthCarrier)
open import DASHI.Quantum.Stone using
  ( FinitelySupportedDepthColimitDomain
  ; StoneSelfAdjoint
  ; onePointDiscreteIdentityDepthSystem
  ; onePointFiniteHamiltonian
  ; onePointFiniteHamiltonianSelfAdjoint
  ; onePointFiniteHilbertSpace
  ; onePointFiniteSupportColimitDomain
  )

-- The depth-0 carrier of the finite tower is the one-point Hilbert space
-- already constructed in Stone.agda.  In this lane the "colimit vector"
-- is therefore concrete, not axiomatic.

ColimitHilbert : HilbertSpace
ColimitHilbert = onePointFiniteHilbertSpace

ColimitVector : Set
ColimitVector = DepthCarrier zero

eigenvalue : Nat → ℝ
eigenvalue n = toℝ n

HNorm : ColimitVector → ℝ
HNorm _ = toℝ 0

HDomain : Set
HDomain = ColimitVector

H : HDomain → ColimitVector
H = onePointFiniteHamiltonian

H-is-canonical :
  (x : HDomain) →
  H x ≡ onePointFiniteHamiltonian x
H-is-canonical _ = refl

colimitGeneratorSelfAdjoint :
  StoneSelfAdjoint ColimitHilbert H
colimitGeneratorSelfAdjoint = onePointFiniteHamiltonianSelfAdjoint

finiteSupportColimitDomain :
  FinitelySupportedDepthColimitDomain onePointDiscreteIdentityDepthSystem
finiteSupportColimitDomain = onePointFiniteSupportColimitDomain

record SelfAdjointColimitGeneratorWitness : Set₁ where
  field
    colimitVector :
      Set

    colimitVectorIsCanonical :
      colimitVector ≡ ColimitVector

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

    witnessBoundary :
      List String

open SelfAdjointColimitGeneratorWitness public

canonicalSelfAdjointColimitGeneratorWitness :
  SelfAdjointColimitGeneratorWitness
canonicalSelfAdjointColimitGeneratorWitness =
  record
    { colimitVector = ColimitVector
    ; colimitVectorIsCanonical = refl
    ; finiteSupportDomain = onePointFiniteSupportColimitDomain
    ; finiteSupportDomainIsCanonical = refl
    ; generator = H
    ; generatorIsCanonical = H-is-canonical
    ; generatorSelfAdjoint = colimitGeneratorSelfAdjoint
    ; witnessBoundary =
        "SelfAdjointGenerator packages the actual one-point Stone Hamiltonian witness"
        ∷ "The depth-0 colimit vector is the concrete one-point carrier from Stone"
        ∷ "The finite-support colimit domain is the inhabited Stone witness onePointFiniteSupportColimitDomain"
        ∷ "Self-adjointness is inherited from the concrete Stone theorem onePointFiniteHamiltonianSelfAdjoint"
        ∷ []
    }

selfAdjointBoundary : List String
selfAdjointBoundary =
  "SelfAdjointGenerator is theorem-bearing: the generator is onePointFiniteHamiltonian"
  ∷ "The finite-support colimit domain is the concrete Stone witness, not a token"
  ∷ "No finite arithmetic or linearity postulates are introduced"
  ∷ []
