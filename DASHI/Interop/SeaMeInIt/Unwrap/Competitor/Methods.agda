module DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Methods where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Core

------------------------------------------------------------------------
-- Closed method universe and family permissions
------------------------------------------------------------------------

data MethodKind : Set where
  equirectangular : MethodKind
  cylindricalEqualArea : MethodKind
  cubedSphere : MethodKind
  octahedralMap : MethodKind
  healpixCarrier : MethodKind
  geodesicIcosaCarrier : MethodKind
  sphericalHarmonics : MethodKind
  healpixSphericalHarmonics : MethodKind
  bt369Sphere : MethodKind
  lscm : MethodKind
  abf : MethodKind
  arap : MethodKind
  slim : MethodKind
  bff : MethodKind
  xatlas : MethodKind
  optCuts : MethodKind
  autoCuts : MethodKind
  ambrosioTortorelli : MethodKind
  blenderUnwrap : MethodKind
  densePoseAtlas : MethodKind
  learnedSemanticUV : MethodKind

methodName : MethodKind → String
methodName equirectangular = "equirectangular"
methodName cylindricalEqualArea = "cylindrical_equal_area"
methodName cubedSphere = "cubed_sphere"
methodName octahedralMap = "octahedral"
methodName healpixCarrier = "healpix"
methodName geodesicIcosaCarrier = "geodesic_icosa"
methodName sphericalHarmonics = "spherical_harmonics"
methodName healpixSphericalHarmonics = "healpix_spherical_harmonics"
methodName bt369Sphere = "bt369_sphere"
methodName lscm = "lscm"
methodName abf = "abf"
methodName arap = "arap"
methodName slim = "slim"
methodName bff = "bff"
methodName xatlas = "xatlas"
methodName optCuts = "optcuts"
methodName autoCuts = "autocuts"
methodName ambrosioTortorelli = "ambrosio_tortorelli"
methodName blenderUnwrap = "blender_unwrap"
methodName densePoseAtlas = "densepose_atlas"
methodName learnedSemanticUV = "learned_semantic_uv"

registeredMethods : List MethodKind
registeredMethods =
  equirectangular
  ∷ cylindricalEqualArea
  ∷ cubedSphere
  ∷ octahedralMap
  ∷ healpixCarrier
  ∷ geodesicIcosaCarrier
  ∷ sphericalHarmonics
  ∷ healpixSphericalHarmonics
  ∷ bt369Sphere
  ∷ lscm
  ∷ abf
  ∷ arap
  ∷ slim
  ∷ bff
  ∷ xatlas
  ∷ optCuts
  ∷ autoCuts
  ∷ ambrosioTortorelli
  ∷ blenderUnwrap
  ∷ densePoseAtlas
  ∷ learnedSemanticUV
  ∷ []

data MethodFamily : Set where
  sphericalRectangleExport : MethodFamily
  sphericalScientificGrid : MethodFamily
  spectralBasis : MethodFamily
  meshParameterizer : MethodFamily
  seamAndCutOptimizer : MethodFamily
  blackBoxArtistTool : MethodFamily
  bodyCorrespondenceAtlas : MethodFamily
  learnedProposal : MethodFamily
  dashiNativeAtlas : MethodFamily

methodFamily : MethodKind → MethodFamily
methodFamily equirectangular = sphericalRectangleExport
methodFamily cylindricalEqualArea = sphericalRectangleExport
methodFamily cubedSphere = sphericalRectangleExport
methodFamily octahedralMap = sphericalRectangleExport
methodFamily healpixCarrier = sphericalScientificGrid
methodFamily geodesicIcosaCarrier = sphericalScientificGrid
methodFamily sphericalHarmonics = spectralBasis
methodFamily healpixSphericalHarmonics = spectralBasis
methodFamily bt369Sphere = dashiNativeAtlas
methodFamily lscm = meshParameterizer
methodFamily abf = meshParameterizer
methodFamily arap = meshParameterizer
methodFamily slim = meshParameterizer
methodFamily bff = meshParameterizer
methodFamily xatlas = meshParameterizer
methodFamily optCuts = seamAndCutOptimizer
methodFamily autoCuts = seamAndCutOptimizer
methodFamily ambrosioTortorelli = seamAndCutOptimizer
methodFamily blenderUnwrap = blackBoxArtistTool
methodFamily densePoseAtlas = bodyCorrespondenceAtlas
methodFamily learnedSemanticUV = learnedProposal

record FamilyAllowedClaims : Set where
  field
    mayClaimUVExport : Bool
    mayClaimSphericalMeasure : Bool
    mayClaimSpectralBasis : Bool
    mayClaimSeamOptimization : Bool
    mayClaimManufacturing : Bool
    mayClaimProposalOnly : Bool

open FamilyAllowedClaims public

allowedClaims : MethodFamily → FamilyAllowedClaims
allowedClaims sphericalRectangleExport =
  record
    { mayClaimUVExport = true
    ; mayClaimSphericalMeasure = false
    ; mayClaimSpectralBasis = false
    ; mayClaimSeamOptimization = false
    ; mayClaimManufacturing = false
    ; mayClaimProposalOnly = false
    }
allowedClaims sphericalScientificGrid =
  record
    { mayClaimUVExport = false
    ; mayClaimSphericalMeasure = true
    ; mayClaimSpectralBasis = false
    ; mayClaimSeamOptimization = false
    ; mayClaimManufacturing = false
    ; mayClaimProposalOnly = false
    }
allowedClaims spectralBasis =
  record
    { mayClaimUVExport = false
    ; mayClaimSphericalMeasure = true
    ; mayClaimSpectralBasis = true
    ; mayClaimSeamOptimization = false
    ; mayClaimManufacturing = false
    ; mayClaimProposalOnly = false
    }
allowedClaims meshParameterizer =
  record
    { mayClaimUVExport = true
    ; mayClaimSphericalMeasure = false
    ; mayClaimSpectralBasis = false
    ; mayClaimSeamOptimization = false
    ; mayClaimManufacturing = false
    ; mayClaimProposalOnly = false
    }
allowedClaims seamAndCutOptimizer =
  record
    { mayClaimUVExport = true
    ; mayClaimSphericalMeasure = false
    ; mayClaimSpectralBasis = false
    ; mayClaimSeamOptimization = true
    ; mayClaimManufacturing = false
    ; mayClaimProposalOnly = false
    }
allowedClaims blackBoxArtistTool =
  record
    { mayClaimUVExport = true
    ; mayClaimSphericalMeasure = false
    ; mayClaimSpectralBasis = false
    ; mayClaimSeamOptimization = false
    ; mayClaimManufacturing = false
    ; mayClaimProposalOnly = false
    }
allowedClaims bodyCorrespondenceAtlas =
  record
    { mayClaimUVExport = true
    ; mayClaimSphericalMeasure = false
    ; mayClaimSpectralBasis = false
    ; mayClaimSeamOptimization = false
    ; mayClaimManufacturing = false
    ; mayClaimProposalOnly = false
    }
allowedClaims learnedProposal =
  record
    { mayClaimUVExport = false
    ; mayClaimSphericalMeasure = false
    ; mayClaimSpectralBasis = false
    ; mayClaimSeamOptimization = false
    ; mayClaimManufacturing = false
    ; mayClaimProposalOnly = true
    }
allowedClaims dashiNativeAtlas =
  record
    { mayClaimUVExport = true
    ; mayClaimSphericalMeasure = true
    ; mayClaimSpectralBasis = false
    ; mayClaimSeamOptimization = true
    ; mayClaimManufacturing = false
    ; mayClaimProposalOnly = false
    }

record CompetitorMethod : Set₁ where
  field
    kind : MethodKind
    source : SurfaceCarrier
    target : TargetCarrier
    mapContract : MapContract source target
    producesUV : Bool
    producesSeams : Bool
    requiresDisk : Bool
    externalTool : Bool
    learnedModel : Bool
    claimBoundary : ClaimBoundary

open CompetitorMethod public
