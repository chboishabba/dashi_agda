module DASHI.Interop.SeaMeInItUnwrapCompetitors where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Everything public

------------------------------------------------------------------------
-- Compatibility facade for the split competitor surface.
------------------------------------------------------------------------

canonicalMethodRegistry :
  registeredMethods
  ≡
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
canonicalMethodRegistry = refl
