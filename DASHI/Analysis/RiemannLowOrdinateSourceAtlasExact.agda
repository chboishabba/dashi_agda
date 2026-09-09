module DASHI.Analysis.RiemannLowOrdinateSourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION FOR THE LOW-ORDINATE RH CERTIFICATE
--
-- The numerical verification source is retained as a source object rather than
-- being promoted into an abstract Agda theorem merely by citation.
------------------------------------------------------------------------

plattTrudgian2021 : Source.AttributedSource
plattTrudgian2021 =
  Source.mkDOISource
    "Dave Platt; Tim Trudgian"
    "The Riemann hypothesis is true up to 3·10^12"
    "Bulletin of the London Mathematical Society 53(3), 792-797"
    "2021"
    "10.1112/blms.12460"
    "https://doi.org/10.1112/blms.12460"
    Source.academicArticleSource
    "source for the rigorous interval-arithmetic verification that all nontrivial zeta zeros with 0 < Im rho <= 3·10^12 lie on Re rho = 1/2 and are simple; the citation does not itself inhabit DASHI's low-ordinate certificate"
    Source.publicAttribution

record LowOrdinateSourceBoundary : Set where
  constructor low-ordinate-source-boundary
  field
    citationIsLowCertificate : Bool
    citationIsLowCertificateIsFalse : citationIsLowCertificate ≡ false
    sourceRangeMatchesAbstractLowPartitionAutomatically : Bool
    sourceRangeMatchesAbstractLowPartitionAutomaticallyIsFalse :
      sourceRangeMatchesAbstractLowPartitionAutomatically ≡ false
    sourceVerificationCreatesRH : Bool
    sourceVerificationCreatesRHIsFalse : sourceVerificationCreatesRH ≡ false

canonicalLowOrdinateSourceBoundary : LowOrdinateSourceBoundary
canonicalLowOrdinateSourceBoundary =
  low-ordinate-source-boundary false refl false refl false refl

plattTrudgianSourceReference : String
plattTrudgianSourceReference =
  "Platt & Trudgian (2021), BLMS 53(3):792-797, DOI 10.1112/blms.12460; source identity and height statement must still be welded to the exact DASHI Low/High partition before use"
