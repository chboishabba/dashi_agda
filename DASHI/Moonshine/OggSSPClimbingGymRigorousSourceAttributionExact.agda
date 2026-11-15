module DASHI.Moonshine.OggSSPClimbingGymRigorousSourceAttributionExact where

------------------------------------------------------------------------
-- CLAIM-BOUNDED SOURCES FOR THE RIGOROUS ZERO / PHASE CERTIFICATE PIPELINE
--
-- Attribution follows the repository-wide rule:
--
--   citation / software documentation / external numerical result
--      != imported Agda proof
--      != Monster authority
--      != Riemann-hypothesis proof inside DASHI.
--
-- External roles are deliberately separated:
-- * FLINT documentation: API / producer semantics for Arb balls and zeta-zero
--   isolation/refinement;
-- * Johansson 2017: ball-arithmetic method/literature authority;
-- * Platt--Trudgian 2021: independent published rigorous RH verification far
--   beyond the first 849 zeros, using interval arithmetic;
-- * LMFDB: independent reference dataset / cross-check, not the producer of
--   DASHI's certificate bytes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

flintManual : Source.AttributedSource
flintManual =
  Source.mkNoDOISource
    "The FLINT team"
    "FLINT: Fast Library for Number Theory; acb_dirichlet / Arb documentation"
    "FLINT documentation and project manual"
    "2026"
    "https://flintlib.org/doc/flint.pdf"
    Source.technicalStandardSource
    "Producer/API authority only: documents Arb ball semantics and the functions that isolate/refine Hardy-Z zeros and compute nontrivial zeta zeros. It does not import a proof object into Agda."
    Source.publicAttribution

johanssonArb2017 : Source.AttributedSource
johanssonArb2017 =
  Source.mkDOISource
    "Fredrik Johansson"
    "Arb: Efficient Arbitrary-Precision Midpoint-Radius Interval Arithmetic"
    "IEEE Transactions on Computers 66(8), 1281-1292"
    "2017"
    "10.1109/TC.2017.2690633"
    "https://doi.org/10.1109/TC.2017.2690633"
    Source.academicArticleSource
    "Method authority for rigorous midpoint-radius ball arithmetic used by the external certificate producer; not theorem import into DASHI."
    Source.publicAttribution

plattTrudgian2021 : Source.AttributedSource
plattTrudgian2021 =
  Source.mkDOISource
    "Dave Platt and Tim Trudgian"
    "The Riemann hypothesis is true up to 3*10^12"
    "Bulletin of the London Mathematical Society 53, 792-797"
    "2021"
    "10.1112/blms.12460"
    "https://doi.org/10.1112/blms.12460"
    Source.academicArticleSource
    "Independent published rigorous numerical context: interval-arithmetic verification of critical-line zeros and simplicity through height 3*10^12. This is external scientific authority, not the producer of the checked-in climbing-gym artifact and not an Agda proof import."
    Source.publicAttribution

lmfdbZetaZeros : Source.AttributedSource
lmfdbZetaZeros =
  Source.mkNoDOISource
    "LMFDB Collaboration"
    "Zeros of the Riemann zeta function"
    "L-functions and Modular Forms Database"
    "2026 access"
    "https://www.lmfdb.org/zeros/zeta/"
    Source.institutionalSource
    "Independent reference/cross-check dataset. The accessed database reports the first 103800788359 zeros and approximately 2.5e-31 ordinate precision; DASHI does not identify those hosted values with its own artifact without an explicit comparison receipt."
    Source.publicAttribution

rigorousZeroSourceAtlas : Source.AttributedSourceAtlas
rigorousZeroSourceAtlas =
  Source.mkSourceAtlas
    "Monster Climbing Gym rigorous zero / phase sources"
    "DASHI.Moonshine.OggSSPClimbingGymRigorousSourceAttributionExact"
    (flintManual ∷ johanssonArb2017 ∷ plattTrudgian2021 ∷ lmfdbZetaZeros ∷ [])
    "Claim-relative provenance for external rigorous interval production and independent zeta-zero cross-checks. No entry imports proof or creates Monster/RH authority."

record RigorousZeroSourceBoundary : Set where
  constructor rigorous-zero-source-boundary
  field
    flintAPIDocumentationAcquired : Bool
    arbMethodPaperAttributed : Bool
    plattTrudgianRigorousContextAttributed : Bool
    lmfdbIndependentReferenceAttributed : Bool

    flintCitationImportsProof : Bool
    flintOutputIsAgdaKernelProof : Bool
    lmfdbIsCertificateProducer : Bool
    lmfdbEqualityToGeneratedBundleEstablished : Bool
    externalRigorousVerificationProvesMonsterSpecificity : Bool
    externalRigorousVerificationPromotesRHInsideDASHI : Bool

open RigorousZeroSourceBoundary public

canonicalRigorousZeroSourceBoundary : RigorousZeroSourceBoundary
canonicalRigorousZeroSourceBoundary =
  rigorous-zero-source-boundary
    true true true true
    false false false false false false
