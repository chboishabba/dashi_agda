module DASHI.Moonshine.SupersingularFrickeSpecialFibreSelectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / GEOMETRIC CONTEXT
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
--
-- Treneer recalls the Deligne--Rapoport/Ogg reduction of X_0(p): two copies of
-- X_0(1) meet at supersingular points, and w_p exchanges the components.  On
-- the supersingular locus it fixes F_p-rational j-invariants and exchanges
-- quadratic Frobenius-conjugate pairs.  The quotient special fibre of X_0^+(p)
-- is therefore one rational component with one self-node for each quadratic
-- pair.
--
-- DASHI CONTRIBUTION
--
-- Turn that geometric description into the exact theorem interface required by
-- the live Ogg selector programme.  A source-facing realization supplies:
--
--   * the actual Frobenius pair count d_F(p);
--   * a one-component rational nodal special fibre whose node count is d_F(p);
--   * equality between the generic genus g(X_0^+(p)) and the arithmetic genus
--     of that proper flat special fibre.
--
-- The generic nodal dual-graph theorem then derives, rather than assumes,
--
--   g(X_0^+(p)) = d_F(p).
--
-- This route is logically independent of the repository's finite
-- Fricke/class-number table.  The missing theorem is now exactly the actual
-- Deligne--Rapoport/Fricke special-fibre realization and flat-genus bridge for
-- arbitrary prime p, not another arithmetic control scan.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.RationalNodalSpecialFibreGenusExact as Nodal

record PrimeFrickeSpecialFibreRealization : Set where
  field
    prime : Nat
    frobeniusPairDefect : Nat
    genericFrickeGenus : Nat

    specialFibre : Nodal.NodalDualGraphGenusData

    nodesAreQuadraticPairs :
      Nodal.nodeCount specialFibre ≡ frobeniusPairDefect

    flatGenusPreservation :
      genericFrickeGenus ≡ Nodal.arithmeticGenus specialFibre

open PrimeFrickeSpecialFibreRealization public

frickeGenusEqualsFrobeniusPairDefect :
  (R : PrimeFrickeSpecialFibreRealization) →
  genericFrickeGenus R ≡ frobeniusPairDefect R
frickeGenusEqualsFrobeniusPairDefect R =
  trans
    (flatGenusPreservation R)
    (trans
      (Nodal.arithmeticGenusEqualsNodeCount (specialFibre R))
      (nodesAreQuadraticPairs R))

zeroFrickeGenusIffZeroFrobeniusPairDefect :
  (R : PrimeFrickeSpecialFibreRealization) →
  genericFrickeGenus R ≡ 0 ↔ frobeniusPairDefect R ≡ 0
zeroFrickeGenusIffZeroFrobeniusPairDefect R =
  (λ genusZero → trans (sym (frickeGenusEqualsFrobeniusPairDefect R)) genusZero)
  ,
  (λ pairZero → trans (frickeGenusEqualsFrobeniusPairDefect R) pairZero)

record SupersingularFrickeSpecialFibreSelectorBoundary : Set where
  field
    nodalSpecialFibreReductionConsumed : Bool
    genericGenusEqualsPairDefectDerived : Bool
    zeroGenusIffAllCoarseSupersingularFixedDerived : Bool
    arbitraryPrimeSpecialFibreRealizationConstructedHere : Bool
    finiteFrickeTableUsedInProof : Bool
    globalMonsterOggEquivalenceClaimedHere : Bool

canonicalSupersingularFrickeSpecialFibreSelectorBoundary :
  SupersingularFrickeSpecialFibreSelectorBoundary
canonicalSupersingularFrickeSpecialFibreSelectorBoundary = record
  { nodalSpecialFibreReductionConsumed = true
  ; genericGenusEqualsPairDefectDerived = true
  ; zeroGenusIffAllCoarseSupersingularFixedDerived = true
  ; arbitraryPrimeSpecialFibreRealizationConstructedHere = false
  ; finiteFrickeTableUsedInProof = false
  ; globalMonsterOggEquivalenceClaimedHere = false
  }
