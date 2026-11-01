module DASHI.Interop.LightCodecTransportDischarge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Combinatorics.TriadicVideoCodecObservationQuotient as Codec
import DASHI.Physics.Closure.LightTransportFibreClosure as Light

------------------------------------------------------------------------
-- Shared discharge for the light-transport and video-codec analogy.
--
-- The common structure is:
--
--   baseline/chart -> latent transform -> residual/defect
--     -> admissibility gates -> deterministic reuse/application
--
-- The analogy is operational, not an identity claim between rendering physics
-- and video compression.

data LightCodecSharedSurface : Set where
  latentTransformSurface : LightCodecSharedSurface
  residualDefectSurface : LightCodecSharedSurface
  quotientReuseSurface : LightCodecSharedSurface
  sideInformationSurface : LightCodecSharedSurface
  deterministicReplaySurface : LightCodecSharedSurface

data LightCodecNonClaim : Set where
  codecIsNotLightPhysics : LightCodecNonClaim
  lightClosureIsNotCodecBenchmark : LightCodecNonClaim
  reuseRequiresReceipt : LightCodecNonClaim
  residualsRemainExplicit : LightCodecNonClaim
  sideInformationIsPartOfTheArtifact : LightCodecNonClaim

canonicalSharedSurfaces : List LightCodecSharedSurface
canonicalSharedSurfaces =
  latentTransformSurface
  ∷ residualDefectSurface
  ∷ quotientReuseSurface
  ∷ sideInformationSurface
  ∷ deterministicReplaySurface
  ∷ []

canonicalLightCodecNonClaims : List LightCodecNonClaim
canonicalLightCodecNonClaims =
  codecIsNotLightPhysics
  ∷ lightClosureIsNotCodecBenchmark
  ∷ reuseRequiresReceipt
  ∷ residualsRemainExplicit
  ∷ sideInformationIsPartOfTheArtifact
  ∷ []

record LightCodecTransportAnalogyDischarge : Set₁ where
  field
    lightSurface :
      Light.LightTransportFibreClosure

    codecSurface :
      Codec.TriadicVideoCodecObservationQuotient

    lightCertificate :
      Light.LightTransportNonPromotionCertificate lightSurface

    codecCertificate :
      Codec.CodecNonPromotionCertificate codecSurface

    sharedSurfaces :
      List LightCodecSharedSurface

    sharedSurfacesAreCanonical :
      sharedSurfaces ≡ canonicalSharedSurfaces

    nonClaims :
      List LightCodecNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalLightCodecNonClaims

    analogyPromotesIdentity :
      Bool

    analogyPromotesIdentityIsFalse :
      analogyPromotesIdentity ≡ false

    dischargeReading :
      String

open LightCodecTransportAnalogyDischarge public

canonicalLightTransportToySurface :
  Light.LightTransportFibreClosure
canonicalLightTransportToySurface =
  record
    { SceneState =
        ⊤
    ; UnlitViewport =
        ⊤
    ; PhotonOrPixelCarrier =
        ⊤
    ; GeometryFibre =
        ⊤
    ; MaterialFibre =
        ⊤
    ; SpectralFibre =
        ⊤
    ; VisibilityFibre =
        ⊤
    ; TransportOperator =
        ⊤
    ; ClosureReceipt =
        ⊤
    ; ResidualDefect =
        ⊤
    ; LitViewport =
        ⊤
    ; baselineViewport =
        λ _ → tt
    ; carrierFromViewport =
        λ _ → tt
    ; geometryFibre =
        λ _ _ → tt
    ; materialFibre =
        λ _ _ → tt
    ; spectralFibre =
        λ _ → tt
    ; visibilityFibre =
        λ _ _ → tt
    ; mixingMode =
        λ _ → Light.diffuseSplit
    ; compositionShape =
        λ _ → Light.cachedClosureChart
    ; closeTransport =
        λ _ _ _ _ → tt
    ; applyClosedTransport =
        λ _ _ → tt
    ; closureReceipt =
        λ _ → tt
    ; residualDefect =
        λ _ _ → tt
    ; residualAdmissible =
        λ _ → ⊤
    ; gateSatisfied =
        λ _ _ → ⊤
    ; pipeline =
        Light.canonicalLightTransportPipeline
    ; transportReading =
        "Toy inhabitant for a closed light transport surface: fibres are explicit and reuse is receipt-gated."
    }

canonicalTriadicVideoCodecToySurface :
  Codec.TriadicVideoCodecObservationQuotient
canonicalTriadicVideoCodecToySurface =
  record
    { FrameStream =
        ⊤
    ; PredictorChart =
        ⊤
    ; SignedResidual =
        ⊤
    ; BalancedPlane =
        ⊤
    ; MagnitudePlane =
        ⊤
    ; SignPlane =
        ⊤
    ; BlockOrbit =
        ⊤
    ; SideInformation =
        ⊤
    ; EntropyPayload =
        ⊤
    ; DecodedFrameStream =
        ⊤
    ; chooseChart =
        λ _ → tt
    ; chartKind =
        λ _ → Codec.temporalDeltaChart
    ; signedResidual =
        λ _ _ → tt
    ; balancedPlanes =
        λ _ → tt ∷ []
    ; symbolOf =
        λ _ → Codec.zeroTrit
    ; magnitudePlane =
        λ _ → tt
    ; signPlane =
        λ _ → tt
    ; reuseAction =
        λ _ → Codec.newBlock
    ; reuseWitness =
        λ _ → tt
    ; encodePayload =
        λ _ _ → tt
    ; decodePayload =
        λ _ _ → tt
    ; sideInformationFor =
        λ _ _ → tt
    ; gateSatisfied =
        λ _ _ → ⊤
    ; sameDecodedStream =
        λ _ _ → ⊤
    ; pipeline =
        Codec.canonicalCodecPipeline
    ; codecReading =
        "Toy inhabitant for a triadic video quotient: residuals, side information, and deterministic decode are explicit."
    }

canonicalLightCodecTransportAnalogyDischarge :
  LightCodecTransportAnalogyDischarge
canonicalLightCodecTransportAnalogyDischarge =
  record
    { lightSurface =
        canonicalLightTransportToySurface
    ; codecSurface =
        canonicalTriadicVideoCodecToySurface
    ; lightCertificate =
        Light.canonicalLightTransportNonPromotionCertificate
          canonicalLightTransportToySurface
    ; codecCertificate =
        Codec.canonicalCodecNonPromotionCertificate
          canonicalTriadicVideoCodecToySurface
    ; sharedSurfaces =
        canonicalSharedSurfaces
    ; sharedSurfacesAreCanonical =
        refl
    ; nonClaims =
        canonicalLightCodecNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; analogyPromotesIdentity =
        false
    ; analogyPromotesIdentityIsFalse =
        refl
    ; dischargeReading =
        "Light transport and triadic video codec share a latent-transform/reuse discipline, but the shared surface is analogy-only and remains non-promoting without receipts."
    }
