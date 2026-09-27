{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologySourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record QuantumMereologySource : Set where
  constructor quantum-mereology-source
  field
    authors title venue year identifier supports : String

open QuantumMereologySource public

carrollSingh2021 : QuantumMereologySource
carrollSingh2021 =
  quantum-mereology-source
    "Sean M. Carroll; Ashmeet Singh"
    "Quantum mereology: Factorizing Hilbert space into subsystems with quasiclassical dynamics"
    "Physical Review A 103, 022213"
    "2021"
    "doi:10.1103/PhysRevA.103.022213"
    "Given Hilbert space plus Hamiltonian, studies preferred tensor-product factorisations using quasiclassical robustness, entanglement-growth and localization criteria."

caoCarrollMichalakis2017 : QuantumMereologySource
caoCarrollMichalakis2017 =
  quantum-mereology-source
    "ChunJun Cao; Sean M. Carroll; Spyridon Michalakis"
    "Space from Hilbert space: Recovering geometry from bulk entanglement"
    "Physical Review D 95, 024031"
    "2017"
    "doi:10.1103/PhysRevD.95.024031"
    "Given an already supplied tensor factorisation, uses entanglement structure and mutual-information-derived graph data to reconstruct emergent spatial geometry and studies curvature response."

pasqualiniFortin2026 : QuantumMereologySource
pasqualiniFortin2026 =
  quantum-mereology-source
    "Matías Pasqualini; Sebastian Fortin"
    "Towards a Tensor Product Structure-Grounded Mereology"
    "Entropy 28(6), 627"
    "2026"
    "doi:10.3390/e28060627"
    "Treats tensor-product structures as the subsystem/mereological architecture and argues that the space of TPSs lacks a canonical global meet analogous to the classical partition lattice."

record QuantumMereologyAttributionBoundary : Set where
  field
    citationCreatesLocalProof : Bool
    citationCreatesLocalProofIsFalse : citationCreatesLocalProof ≡ false

    sourceClaimCreatesPreferredFactorisation : Bool
    sourceClaimCreatesPreferredFactorisationIsFalse :
      sourceClaimCreatesPreferredFactorisation ≡ false

    geometryPaperCreatesFullSpacetimeGR : Bool
    geometryPaperCreatesFullSpacetimeGRIsFalse :
      geometryPaperCreatesFullSpacetimeGR ≡ false

    noCanonicalMeetClaimImportedAsKernelTheorem : Bool
    noCanonicalMeetClaimImportedAsKernelTheoremIsFalse :
      noCanonicalMeetClaimImportedAsKernelTheorem ≡ false

canonicalQuantumMereologyAttributionBoundary :
  QuantumMereologyAttributionBoundary
canonicalQuantumMereologyAttributionBoundary = record
  { citationCreatesLocalProof = false
  ; citationCreatesLocalProofIsFalse = refl
  ; sourceClaimCreatesPreferredFactorisation = false
  ; sourceClaimCreatesPreferredFactorisationIsFalse = refl
  ; geometryPaperCreatesFullSpacetimeGR = false
  ; geometryPaperCreatesFullSpacetimeGRIsFalse = refl
  ; noCanonicalMeetClaimImportedAsKernelTheorem = false
  ; noCanonicalMeetClaimImportedAsKernelTheoremIsFalse = refl
  }
