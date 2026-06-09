module DASHI.Physics.SFGC.NonAbelian.SU3ColorSectorNote where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.SFGC.NonAbelian.NonAbelianSFGCCarrier using
  ( NonAbelianSFGCCarrierWitness
  ; canonicalNonAbelianSFGCCarrierWitness
  )
open import DASHI.Physics.SFGC.NonAbelian.DepthQuotientIso using
  ( DepthQuotientWitness
  ; canonicalDepthQuotientWitness
  )

------------------------------------------------------------------------
-- SU(3) / W3 route note for the finite nonabelian SFGC carrier.
--
-- This module stays in the real SFGC namespace and documents the path
-- from the existing nonabelian finite carrier to the eventual SU(3)
-- extension. The current carrier surface already exposes the graded lane
-- witness, the even Clifford basis, and the selected depth quotient:
--
--   * DASHI.Physics.SFGC.NonAbelian.NonAbelianSFGCCarrier
--   * DASHI.Physics.SFGC.NonAbelian.DepthQuotientIso
--
-- Those modules give the finite nonabelian anchor. The remaining SU(3)
-- step is best understood as a W3 / clock-and-shift route: build the
-- 3-generator Weyl-Heisenberg algebra, then identify its 3x3 matrix
-- realization as the next nonabelian sector.
--
-- The file is intentionally concrete: it records the canonical carrier
-- and depth-quotient witnesses and checks one finite arithmetic fact.

record SU3ColorSectorRouteNote : Set₁ where
  field
    carrierWitness :
      NonAbelianSFGCCarrierWitness

    carrierWitnessIsCanonical :
      carrierWitness ≡ canonicalNonAbelianSFGCCarrierWitness

    depthQuotientWitness :
      DepthQuotientWitness

    depthQuotientWitnessIsCanonical :
      depthQuotientWitness ≡ canonicalDepthQuotientWitness

    routeSummary :
      String

    w3SeedProduct :
      Nat

    w3SeedProductReduces :
      w3SeedProduct ≡ 7 * 11 * 13

    w3SeedProductValue :
      w3SeedProduct ≡ 1001

canonicalSU3ColorSectorRouteNote :
  SU3ColorSectorRouteNote
canonicalSU3ColorSectorRouteNote =
  record
    { carrierWitness =
        canonicalNonAbelianSFGCCarrierWitness
    ; carrierWitnessIsCanonical =
        refl
    ; depthQuotientWitness =
        canonicalDepthQuotientWitness
    ; depthQuotientWitnessIsCanonical =
        refl
    ; routeSummary =
        "Finite nonabelian SFGC carrier first, then W3/clock-shift as the SU(3) route."
    ; w3SeedProduct =
        7 * 11 * 13
    ; w3SeedProductReduces =
        refl
    ; w3SeedProductValue =
        refl
    }

open SU3ColorSectorRouteNote public
