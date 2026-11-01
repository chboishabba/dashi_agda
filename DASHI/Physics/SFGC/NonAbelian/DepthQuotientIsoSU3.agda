module DASHI.Physics.SFGC.NonAbelian.DepthQuotientIsoSU3 where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.QFT.W3ToM3Iso using
  (W3ToM3Iso; canonicalW3ToM3Iso)
open import DASHI.Physics.SFGC.NonAbelian.DepthQuotientIso using
  (DepthQuotientWitness; canonicalDepthQuotientWitness)
open import DASHI.Physics.SFGC.NonAbelian.NonAbelianSFGCCarrier using
  (NonAbelianSFGCCarrierWitness; canonicalNonAbelianSFGCCarrierWitness)
open import DASHI.Physics.SFGC.NonAbelian.SU3ColorSectorNote using
  (SU3ColorSectorRouteNote; canonicalSU3ColorSectorRouteNote)

record DepthQuotientIsoSU3Witness : Set₁ where
  field
    w3ToM3Iso :
      W3ToM3Iso

    carrierWitness :
      NonAbelianSFGCCarrierWitness

    depthQuotientWitness :
      DepthQuotientWitness

    routeNote :
      SU3ColorSectorRouteNote

    witnessBoundary :
      List String

open DepthQuotientIsoSU3Witness public

canonicalDepthQuotientIsoSU3Witness : DepthQuotientIsoSU3Witness
canonicalDepthQuotientIsoSU3Witness =
  record
    { w3ToM3Iso = canonicalW3ToM3Iso
    ; carrierWitness = canonicalNonAbelianSFGCCarrierWitness
    ; depthQuotientWitness = canonicalDepthQuotientWitness
    ; routeNote = canonicalSU3ColorSectorRouteNote
    ; witnessBoundary =
        "DepthQuotientIsoSU3 packages the concrete W3-to-M3 bridge"
        ∷ "It reuses the existing nonabelian carrier and selected depth quotient witnesses"
        ∷ "The SU(3) route note remains the honest frontier description"
        ∷ []
    }

depthQuotientIsoSU3Boundary : List String
depthQuotientIsoSU3Boundary =
  "DepthQuotientIsoSU3 is a concrete packaging witness for the SU(3) bridge"
  ∷ []
