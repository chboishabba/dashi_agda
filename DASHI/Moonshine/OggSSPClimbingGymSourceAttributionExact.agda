module DASHI.Moonshine.OggSSPClimbingGymSourceAttributionExact where

------------------------------------------------------------------------
-- ATTRIBUTION / ACQUISITION BOUNDARY FOR THE JMD MONSTER CLIMBING GYM
--
-- This owner deliberately separates three different source relationships:
--
-- 1. the user/JMD-supplied figure is the source of the displayed rows and
--    rounded shift-control labels;
-- 2. mpmath documentation describes the `zetazero(n)` numerical generator
--    used for the checked-in diagnostic cache;
-- 3. LMFDB supplies an independent external reference dataset for zeta zeros.
--
-- None of these citations imports a theorem or creates mathematical authority.
-- In particular, the checked-in cache was generated numerically with mpmath;
-- it was NOT imported row-by-row from LMFDB, and no bytewise/cache-wide LMFDB
-- equality theorem is asserted here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

jmdSuppliedClimbingGymFigure : Source.AttributedSource
jmdSuppliedClimbingGymFigure =
  Source.mkNoDOISource
    "JMD / user-supplied project material"
    "The Monster Climbing Gym — Hole Visualizations"
    "conversation/project attachment"
    "2026"
    "controlled conversation attachment; no public canonical URL asserted"
    (Source.namedSourceKind "user-supplied figure")
    "source of the displayed wall forms, hole counts, mutual-pair counts, rounded shift-control summaries, and explanatory captions only"
    Source.controlledAttribution

mpmathZetaZeroDocumentation : Source.AttributedSource
mpmathZetaZeroDocumentation =
  Source.mkNoDOISource
    "Fredrik Johansson and mpmath contributors"
    "mpmath documentation, Release 1.3.0 — zetazero"
    "mpmath official documentation"
    "2023"
    "https://mpmath.org/doc/current/mpmath.pdf"
    (Source.namedSourceKind "software documentation")
    "documents the zetazero(n) numerical generator and Release 1.3.0 API used as the declared producer class for the diagnostic first-849-zero cache; does not certify this cache, prove zero completeness, or prove RH"
    Source.publicAttribution

lmfdbZetaZeroReference : Source.AttributedSource
lmfdbZetaZeroReference =
  Source.mkNoDOISource
    "LMFDB Collaboration"
    "Zeros of zeta(s)"
    "L-functions and Modular Forms Database"
    "2026 access"
    "https://www.lmfdb.org/zeros/zeta/"
    Source.institutionalSource
    "independent external reference dataset for Riemann-zeta zero ordinates; not the producer of the checked-in cache and not imported as theorem authority"
    Source.publicAttribution

climbingGymSourceAtlas : Source.AttributedSourceAtlas
climbingGymSourceAtlas =
  Source.mkSourceAtlas
    "JMD Monster Climbing Gym source atlas"
    "DASHI.Moonshine.OggSSPClimbingGymSourceAttributionExact"
    (jmdSuppliedClimbingGymFigure
      ∷ mpmathZetaZeroDocumentation
      ∷ lmfdbZetaZeroReference
      ∷ [])
    "bounded provenance for the supplied figure, the numerical zero generator documentation, and one independent external zero-data reference"

------------------------------------------------------------------------
-- Exact repository artifact coordinate for the diagnostic cache.
--
-- The blob id is repository integrity metadata for the bytes observed on this
-- branch.  It is not a mathematical checksum theorem about the truth of the
-- ordinates.  The executable loader separately checks schema/generator/scale,
-- declared count, positivity and strict ordering before replay.
------------------------------------------------------------------------

zeroCacheRepositoryPath : String
zeroCacheRepositoryPath =
  "scripts/data/monster_climbing_gym_first_849_zeros.json"

zeroCacheObservedGitBlob : String
zeroCacheObservedGitBlob =
  "f2df3e2bfade9cac1ea948bcb848d13a3927e4f4"

zeroCacheSchemaVersion : String
zeroCacheSchemaVersion = "1.0.0"

zeroCacheDeclaredGenerator : String
zeroCacheDeclaredGenerator = "mpmath.zetazero"

record ClimbingGymSourceAttributionBoundary : Set where
  constructor climbing-gym-source-attribution-boundary
  field
    suppliedFigureTypedAsSource : Bool
    mpmathGeneratorDocumentationTypedAsSource : Bool
    lmfdbReferenceTypedAsSource : Bool
    mpmathDocumentationReleaseIs130 : Bool
    exactCacheRepositoryArtifactPinned : Bool
    executableCacheMetadataValidationPresent : Bool

    exactRuntimePackageVersionIndependentlyReceipted : Bool
    cacheValuesImportedFromLMFDB : Bool
    cacheWideEqualityAgainstLMFDBEstablished : Bool
    mpmathCacheIsFormalZeroCertificate : Bool
    lmfdbCitationImportsProof : Bool
    sourceFigureSuppliesExactRandomShiftSeed : Bool
    citationCreatesMonsterAuthority : Bool
    citationCreatesRiemannHypothesisAuthority : Bool
    unmergedSiblingTheoremAuthorityImported : Bool

open ClimbingGymSourceAttributionBoundary public

canonicalClimbingGymSourceAttributionBoundary : ClimbingGymSourceAttributionBoundary
canonicalClimbingGymSourceAttributionBoundary =
  climbing-gym-source-attribution-boundary
    true   -- supplied figure is explicitly attributed
    true   -- mpmath docs are explicitly attributed
    true   -- LMFDB external reference is explicitly attributed
    true   -- the cited official documentation is Release 1.3.0
    true   -- exact branch cache path and observed git blob are recorded
    true   -- executable loader validates schema/generator/scale/count/order
    false  -- this source owner does not manufacture a runtime environment receipt
    false  -- cache was generated with mpmath, not copied from LMFDB
    false  -- no complete cache-wide LMFDB equality check is claimed
    false  -- numerical generation is not a formal zero certificate
    false  -- AttributedSource citations are non-promoting by construction
    false  -- the supplied rounded controls do not provide a shift list/seed
    false  -- source citation does not create Monster authority
    false  -- source citation does not create RH authority
    false  -- live sibling PRs are design donors only unless merged

climbingGymSourceAtlasReceiptNonPromoting :
  Source.atlasCreatesAuthority climbingGymSourceAtlas ≡ false
climbingGymSourceAtlasReceiptNonPromoting = refl

mpmathCitationNonPromoting :
  Source.citationImportsProof mpmathZetaZeroDocumentation ≡ false
mpmathCitationNonPromoting = refl

lmfdbCitationNonPromoting :
  Source.citationCreatesAuthority lmfdbZetaZeroReference ≡ false
lmfdbCitationNonPromoting = refl
