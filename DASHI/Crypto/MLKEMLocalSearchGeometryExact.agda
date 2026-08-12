module DASHI.Crypto.MLKEMLocalSearchGeometryExact where

------------------------------------------------------------------------
-- ML-KEM / MLWE LOCAL SEARCH GEOMETRY INTERFACE
--
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Oded Regev, "On lattices, learning with errors, random linear codes, and
-- cryptography", STOC 2005. DOI: 10.1145/1060590.1060603.
--
-- This composes the existing candidate-residual test with exact transformed
-- coordinates, but deliberately does not assert that FIPS-203 NTT coordinates
-- are independently searchable.
------------------------------------------------------------------------

open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Crypto.MLWEKeyStateResidualExact as MLWE
import DASHI.Crypto.TransformLocalFibreGeometryExact as Transform

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

    smallResidualFactors : ∀ error →
      MLWE.Small state error →
      let coordinates = Transform.encode transform (residualToCarrier error)
          locals = splitResidual coordinates
      in LocalSmall₀ (proj₁ locals) ×
         (LocalSmall₁ (proj₂ locals) × Coupling (proj₁ locals) (proj₂ locals))

open MLWELocalCoordinateBridge public

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

-- CandidateSearch returns a plausible secret only. Exact identification still
-- requires a uniqueness theorem such as UniqueResidualIdentification.
