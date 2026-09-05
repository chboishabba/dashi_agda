module DASHI.Analysis.TrigonometricPythagoreanSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED SOURCE AUTHORITY: SIN^2 + COS^2 = 1
--
-- SOURCE:
-- NIST Digital Library of Mathematical Functions, §4.21(ii), Eq. 4.21.12:
--
--   sin^2(z) + cos^2(z) = 1.
--
-- The identity is SOURCEBACKED for the classical DLMF trigonometric functions.
-- It is not automatically an identity for any locally constructed series with
-- matching names or coefficients.
------------------------------------------------------------------------

record TrigonometricPythagoreanSourceAuthority : Set where
  field
    sourceName : String
    sourceLocator : String
    pythagoreanIdentityStated : Set
    classicalSinCosObject : Set
    sourceBackedOnly : Set
    reading : String

open TrigonometricPythagoreanSourceAuthority public

canonicalTrigonometricPythagoreanAuthority :
  TrigonometricPythagoreanSourceAuthority
canonicalTrigonometricPythagoreanAuthority = record
  { sourceName = "NIST DLMF §4.21(ii), Eq. 4.21.12"
  ; sourceLocator = "https://dlmf.nist.gov/4.21.E12"
  ; pythagoreanIdentityStated = ⊤
  ; classicalSinCosObject = ⊤
  ; sourceBackedOnly = ⊤
  ; reading =
      "DLMF source-backs sin^2+cos^2=1 for its classical trigonometric functions; transport to Round11 Bishop sine/cosine requires the same-function weld."
  }

data ClassicalTrigIdentityAutomaticallyAppliesToBishopSeries : Set where

classicalIdentityNeedsSameFunctionWeld :
  ClassicalTrigIdentityAutomaticallyAppliesToBishopSeries → ⊥
classicalIdentityNeedsSameFunctionWeld ()
