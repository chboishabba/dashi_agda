module DASHI.Analysis.ZetaEulerMaclaurinContinuationSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED SOURCE AUTHORITY FOR EULER--MACLAURIN CONTINUATION OF ZETA
--
-- SOURCE:
-- NIST DLMF §25.2, Eq. 25.2.10.
-- The Euler--Maclaurin representation extends zeta to Re(s) > -2n for each
-- positive n, with Bernoulli correction terms and a periodic-Bernoulli
-- remainder integral.  Taking n >= 2 covers s = -3.
--
-- This is SOURCEBACKED analytic authority only.  No internal DASHI proof of
-- the remainder-integral theorem or meromorphic continuation is claimed.
------------------------------------------------------------------------

record ZetaEulerMaclaurinContinuationSourceAuthority : Set where
  field
    sourceName : String
    sourceLocator : String
    eulerMaclaurinRepresentationStated : Set
    continuationHalfPlaneContainsMinusThree : Set
    bernoulliCorrectionTermsPresent : Set
    remainderIntegralPresent : Set
    sourceBackedOnly : Set
    reading : String

open ZetaEulerMaclaurinContinuationSourceAuthority public

canonicalZetaEulerMaclaurinAuthority :
  ZetaEulerMaclaurinContinuationSourceAuthority
canonicalZetaEulerMaclaurinAuthority = record
  { sourceName = "NIST DLMF §25.2, Eq. 25.2.10"
  ; sourceLocator = "https://dlmf.nist.gov/25.2.E10"
  ; eulerMaclaurinRepresentationStated = ⊤
  ; continuationHalfPlaneContainsMinusThree = ⊤
  ; bernoulliCorrectionTermsPresent = ⊤
  ; remainderIntegralPresent = ⊤
  ; sourceBackedOnly = ⊤
  ; reading = "DLMF source-backs an Euler--Maclaurin continuation formula whose domain reaches s=-3; the internal remainder estimate and same-object Casimir finite-part weld remain separate."
  }

data EulerMaclaurinSourceAutomaticallyIsInternalContinuation : Set where

sourceContinuationDoesNotBecomeMachineContinuation :
  EulerMaclaurinSourceAutomaticallyIsInternalContinuation → ⊥
sourceContinuationDoesNotBecomeMachineContinuation ()
