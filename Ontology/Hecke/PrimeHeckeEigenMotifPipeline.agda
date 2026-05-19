module Ontology.Hecke.PrimeHeckeEigenMotifPipeline where

open import Agda.Builtin.Nat using (Nat)

open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.Scan using (State; HeckeFamily; HeckeFamilyOn; Sig15; scan; scanOn)

data EigenClass : Set where
  Earth Spoke Hub : EigenClass

record EigenProfile : Set where
  constructor eigenProfile
  field
    earth : Nat
    spoke : Nat
    hub   : Nat

open EigenProfile public

-- Prime embedding, Hecke scan, eigen clustering, and motif assignment stay in
-- one interface so delta scoring can be phrased in the same basis.
record PrimeHeckeEigenMotifPipelineOn (HeckeState Motif : Set) : Set₁ where
  field
    primeEmbedding : HeckeState → FactorVec
    hecke : HeckeFamilyOn HeckeState

    ΔState : Set
    Δ : HeckeState → HeckeState → ΔState

    signatureEigenProfile : Sig15 → EigenProfile
    deltaEigenProfile : ΔState → EigenProfile
    motifOf : EigenProfile → Motif
    resonance : ΔState → ΔState → Set

  signature : HeckeState → Sig15
  signature s = scanOn hecke s

  motif : HeckeState → Motif
  motif s = motifOf (signatureEigenProfile (signature s))

PrimeHeckeEigenMotifPipeline : Set → Set₁
PrimeHeckeEigenMotifPipeline Motif = PrimeHeckeEigenMotifPipelineOn State Motif

legacyScanPipeline :
  ∀ {Motif : Set} →
  PrimeHeckeEigenMotifPipeline Motif →
  State →
  Sig15
legacyScanPipeline p = PrimeHeckeEigenMotifPipelineOn.signature p

open PrimeHeckeEigenMotifPipelineOn public
