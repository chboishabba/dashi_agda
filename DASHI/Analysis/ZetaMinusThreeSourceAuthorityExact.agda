module DASHI.Analysis.ZetaMinusThreeSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED SOURCE AUTHORITY FOR zeta(-3)
--
-- SOURCE:
-- NIST Digital Library of Mathematical Functions, §25.6(i), Eq. 25.6.3:
--   zeta(-n) = - B_(n+1)/(n+1),  n = 1,2,...
-- URL: https://dlmf.nist.gov/25.6.E3
--
-- For n = 3 this gives zeta(-3) = -B4/4.  Together with B4 = -1/30,
-- the adjacent arithmetic owner compiles the rational value 1/120.
--
-- This module records SOURCEBACKED analytic authority only.  It is not a
-- machine proof of analytic continuation inside DASHI.
------------------------------------------------------------------------

record ZetaMinusThreeSourceAuthority : Set where
  field
    sourceName : String
    sourceLocator : String
    sourceStatesNegativeIntegerBernoulliFormula : Set
    nEqualsThreeInstantiation : Set
    zetaMinusThreeEqualsMinusB4OverFour : Set
    sourceBackedOnly : Set
    reading : String

open ZetaMinusThreeSourceAuthority public

nistDLMFZetaMinusThreeAuthority : ZetaMinusThreeSourceAuthority
nistDLMFZetaMinusThreeAuthority = record
  { sourceName = "NIST DLMF §25.6(i), Eq. 25.6.3"
  ; sourceLocator = "https://dlmf.nist.gov/25.6.E3"
  ; sourceStatesNegativeIntegerBernoulliFormula = ⊤
  ; nEqualsThreeInstantiation = ⊤
  ; zetaMinusThreeEqualsMinusB4OverFour = ⊤
  ; sourceBackedOnly = ⊤
  ; reading = "DLMF source-backs zeta(-3) = -B4/4; internal analytic-continuation proof remains separate."
  }

data SourceAuthorityAutomaticallyBecomesMachineProof : Set where

sourceBackedIsNotMachineOwned :
  SourceAuthorityAutomaticallyBecomesMachineProof → ⊥
sourceBackedIsNotMachineOwned ()
