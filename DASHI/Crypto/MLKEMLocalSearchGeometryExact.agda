module DASHI.Crypto.MLKEMLocalSearchGeometryExact where

------------------------------------------------------------------------
-- ML-KEM / MLWE LOCAL SEARCH GEOMETRY INTERFACE
--
-- This module composes the existing candidate-residual test with the new exact
-- transform/search-factorisation boundaries.  It deliberately stops before a
-- false claim that FIPS-203 NTT coordinates are independently searchable.
--
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Oded Regev, "On lattices, learning with errors, random linear codes, and
-- cryptography", STOC 2005. DOI: 10.1145/1060590.1060603.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)

import DASHI.Crypto.MLWEKeyStateResidualExact as MLWE
import DASHI.Crypto.TransformLocalFibreGeometryExact as Transform
import DASHI.Crypto.SearchFactorisationExact as Search

record MLWELocalCoordinateBridge
    (state : MLWE.NoisyLinearKeyState) : Set₁ where
  constructor mlweLocalCoordinateBridge
  field
    transform : Transform.ExactCoordinateTransform
    residualToCarrier : MLWE.Error state → Transform.Carrier transform
    Local₀ Local₁ : Set
    splitResidual : Transform.Coordinates transform → Local₀ × Local₁
    LocalSmall₀ : Local₀ → Set
    LocalSmall₁ : Local₁ → Set
    Coupling : Local₀ → Local₁ → Set

    -- This is the exact obligation that would have to be discharged against
    -- the concrete ML-KEM residual representation before local testing is used
    -- as an actual cryptanalytic decomposition.
    smallResidualFactors : ∀ error →
      MLWE.Small state error →
      let coordinates = Transform.encode transform (residualToCarrier error)
          locals = splitResidual coordinates
      in LocalSmall₀ (Data.Product.proj₁ locals) ×
         (LocalSmall₁ (Data.Product.proj₂ locals) ×
          Coupling (Data.Product.proj₁ locals) (Data.Product.proj₂ locals))

open MLWELocalCoordinateBridge public

------------------------------------------------------------------------
-- Search-asymmetry dependency graph: cheap residual testing is already known;
-- efficient local enumeration and efficient reconciliation are extra evidence.
------------------------------------------------------------------------

record MLWESearchCollapseCertificate
    (state : MLWE.NoisyLinearKeyState)
    (bridge : MLWELocalCoordinateBridge state) : Set₁ where
  constructor mlweSearchCollapseCertificate
  field
    LocalWitness₀ LocalWitness₁ : Set
    enumerate₀ : MLWE.Public state → LocalWitness₀
    enumerate₁ : MLWE.Public state → LocalWitness₁
    Reconciled : LocalWitness₀ → LocalWitness₁ → Set
    reconcile : ∀ public → Reconciled (enumerate₀ public) (enumerate₁ public)
    recoverSecret : LocalWitness₀ → LocalWitness₁ → MLWE.Secret state
    recoveredCandidatePlausible : ∀ public →
      MLWE.CandidatePlausible state public
        (recoverSecret (enumerate₀ public) (enumerate₁ public))

open MLWESearchCollapseCertificate public

collapseCertificateGivesCandidateSearch :
  ∀ {state : MLWE.NoisyLinearKeyState}
    {bridge : MLWELocalCoordinateBridge state} →
  MLWESearchCollapseCertificate state bridge →
  MLWE.CandidateSearch state
collapseCertificateGivesCandidateSearch certificate =
  MLWE.candidateSearch
    (λ public → recoverSecret certificate
      (enumerate₀ certificate public) (enumerate₁ certificate public))
    (recoveredCandidatePlausible certificate)

-- Important boundary: CandidateSearch only returns a plausible secret.  Exact
-- identification still requires a uniqueness theorem such as the repository's
-- UniqueResidualIdentification.  Plausibility alone is not key recovery.
