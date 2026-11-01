module Ontology.Hecke.FactorVecSignedScan where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Nat      using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_)

open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.Scan as HS
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM
open import Ontology.Hecke.FactorVecSignedTransport using
  (legalTransfer; transportOrStay)

------------------------------------------------------------------------
-- Signed transport viewed as a Hecke scan family on the prime-address carrier.

factorVecSignedHecke : HS.HeckeFamilyOn FactorVec
factorVecSignedHecke = record
  { T      = transportOrStay
  ; compat = legalTransfer
  }

factorVecSignedSignature : FactorVec → HS.Sig15
factorVecSignedSignature = HS.scanOn factorVecSignedHecke

bit : Bool → Nat
bit false = zero
bit true  = suc zero

signatureTrueCount : HS.Sig15 → Nat
signatureTrueCount (HS.sig15 b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71) =
  bit b2 + bit b3 + bit b5 + bit b7 + bit b11
    + bit b13 + bit b17 + bit b19 + bit b23 + bit b29
    + bit b31 + bit b41 + bit b47 + bit b59 + bit b71

signatureBlocks : HS.Sig15 → PHEM.EigenProfile
signatureBlocks (HS.sig15 b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71) =
  PHEM.eigenProfile
    (bit b2 + bit b3 + bit b5 + bit b7 + bit b11)
    (bit b13 + bit b17 + bit b19 + bit b23 + bit b29)
    (bit b31 + bit b41 + bit b47 + bit b59 + bit b71)

data SignedMotif : Set where
  Rigid Mixed Flowing : SignedMotif

motifOfTrueCount : Nat → SignedMotif
motifOfTrueCount zero = Rigid
motifOfTrueCount (suc zero) = Mixed
motifOfTrueCount (suc (suc zero)) = Mixed
motifOfTrueCount (suc (suc (suc n))) = Flowing

factorVecSignedMotifOf : PHEM.EigenProfile → SignedMotif
factorVecSignedMotifOf ep =
  motifOfTrueCount
    (PHEM.EigenProfile.earth ep
      + PHEM.EigenProfile.spoke ep
      + PHEM.EigenProfile.hub ep)

factorVecSignedPipeline :
  PHEM.PrimeHeckeEigenMotifPipelineOn FactorVec SignedMotif
factorVecSignedPipeline = record
  { primeEmbedding         = λ v → v
  ; hecke                  = factorVecSignedHecke
  ; ΔState                 = HS.Sig15
  ; Δ                      = λ _ y → factorVecSignedSignature y
  ; signatureEigenProfile  = signatureBlocks
  ; deltaEigenProfile      = signatureBlocks
  ; motifOf                = factorVecSignedMotifOf
  ; resonance              = _≡_
  }

factorVecSignedMotif : FactorVec → SignedMotif
factorVecSignedMotif = PHEM.PrimeHeckeEigenMotifPipelineOn.motif factorVecSignedPipeline
