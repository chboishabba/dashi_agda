module DASHI.Analysis.PowerSeriesTermwiseDifferentiationSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED SOURCE AUTHORITY: TERM-BY-TERM POWER-SERIES DIFFERENTIATION
--
-- SOURCE:
-- NIST Digital Library of Mathematical Functions, §1.9(vi), especially
-- Eq. 1.9.63.  DLMF states that inside the circle of convergence a power
-- series represents an analytic function and can be differentiated any number
-- of times term-by-term.  The surrounding subsection also states absolute and
-- uniform convergence on every closed subdisc |z-z0| <= rho < R.
--
-- This module records SOURCEBACKED authority only.  It does not identify a
-- classical complex derivative with any local DASHI/Bishop derivative notion.
------------------------------------------------------------------------

record PowerSeriesDifferentiationSourceAuthority : Set where
  field
    sourceName : String
    sourceLocator : String

    powerSeriesAnalyticInsideRadius : Set
    compactSubdiscUniformConvergence : Set
    termwiseDifferentiationInsideRadius : Set
    arbitraryFiniteDerivativeOrder : Set

    sourceBackedOnly : Set
    reading : String

open PowerSeriesDifferentiationSourceAuthority public

canonicalPowerSeriesDifferentiationAuthority :
  PowerSeriesDifferentiationSourceAuthority
canonicalPowerSeriesDifferentiationAuthority = record
  { sourceName = "NIST DLMF §1.9(vi), Eq. 1.9.63"
  ; sourceLocator = "https://dlmf.nist.gov/1.9.E63"
  ; powerSeriesAnalyticInsideRadius = ⊤
  ; compactSubdiscUniformConvergence = ⊤
  ; termwiseDifferentiationInsideRadius = ⊤
  ; arbitraryFiniteDerivativeOrder = ⊤
  ; sourceBackedOnly = ⊤
  ; reading =
      "DLMF source-backs term-by-term differentiation of a power series inside its radius of convergence; local Bishop carrier, radius and derivative-semantics welds remain explicit."
  }

data SourcePowerSeriesTheoremAutomaticallyIsBishopFactorDerivative : Set where

sourceDoesNotAutoChooseConstructiveDerivative :
  SourcePowerSeriesTheoremAutomaticallyIsBishopFactorDerivative → ⊥
sourceDoesNotAutoChooseConstructiveDerivative ()
