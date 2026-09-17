module DASHI.Moonshine.JInvariantEisensteinDivisorPowerSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- ATTRIBUTED SOURCE ATLAS
--
-- Classical modular-form context is separated from executable finite divisor
-- arithmetic.  The two OEIS entries are independent sequence/parity locators,
-- not definitions or theorem authority.
------------------------------------------------------------------------

serre : Source.AttributedSource
serre =
  Source.mkDOISource
    "Jean-Pierre Serre"
    "A Course in Arithmetic"
    "Graduate Texts in Mathematics 7, Springer"
    "1973"
    "10.1007/978-1-4684-9884-4"
    "https://doi.org/10.1007/978-1-4684-9884-4"
    Source.academicBookSource
    "classical modular-form and Eisenstein-series context reused for the normalized E4/E6 q-expansion coordinate; citation does not prove the local executable recurrence"
    Source.publicAttribution

miyake : Source.AttributedSource
miyake =
  Source.mkDOISource
    "Toshitsune Miyake"
    "Modular Forms"
    "Springer Monographs in Mathematics, Springer"
    "2006"
    "10.1007/3-540-29593-3"
    "https://doi.org/10.1007/3-540-29593-3"
    Source.academicBookSource
    "classical modular-form and Eisenstein-series context reused for normalized E4/E6 and discriminant coordinates; citation does not import convergence or same-object authority"
    Source.publicAttribution

sigma3OEIS : Source.AttributedSource
sigma3OEIS =
  Source.mkNoDOISource
    "N. J. A. Sloane; R. K. Guy"
    "A001158: sigma_3(n), sum of cubes of divisors of n"
    "The On-Line Encyclopedia of Integer Sequences"
    ""
    "https://oeis.org/A001158"
    (Source.namedSourceKind "OEIS sequence record")
    "independent sequence-identity and finite-prefix parity coordinate for the repository's internally computed sigma3; not used to define sigma3 or to create modular-form authority"
    Source.publicAttribution

sigma5OEIS : Source.AttributedSource
sigma5OEIS =
  Source.mkNoDOISource
    "N. J. A. Sloane"
    "A001160: sigma_5(n), sum of fifth powers of divisors of n"
    "The On-Line Encyclopedia of Integer Sequences"
    ""
    "https://oeis.org/A001160"
    (Source.namedSourceKind "OEIS sequence record")
    "independent sequence-identity and finite-prefix parity coordinate for the repository's internally computed sigma5; not used to define sigma5 or to create modular-form authority"
    Source.publicAttribution

canonicalEisensteinDivisorPowerAtlas : Source.AttributedSourceAtlas
canonicalEisensteinDivisorPowerAtlas =
  Source.mkSourceAtlas
    "Eisenstein divisor-power source atlas"
    "DASHI.Moonshine.JInvariantEisensteinDivisorPowerSourceAtlasExact"
    (serre ∷ miyake ∷ sigma3OEIS ∷ sigma5OEIS ∷ [])
    "separates classical normalized Eisenstein-series source context from executable divisor-power arithmetic and OEIS finite-prefix parity coordinates"

sigma3OEISParityOnly : Bool
sigma3OEISParityOnly = true

sigma5OEISParityOnly : Bool
sigma5OEISParityOnly = true

classicalCoefficientAuthoritySeparatedFromFiniteArithmetic : Bool
classicalCoefficientAuthoritySeparatedFromFiniteArithmetic = true

record EisensteinDivisorPowerAttributionBoundary : Set where
  constructor eisenstein-divisor-power-attribution-boundary
  field
    classicalSourcesIdentified : Bool
    sourceDOIsRecorded : Bool
    oeisIdentifiersRecorded : Bool
    oeisUsedOnlyForParity : Bool
    citationsImportProof : Bool
    citationsCreateAuthority : Bool
    finitePrefixParityCreatesInfiniteSeries : Bool
    reading : String
open EisensteinDivisorPowerAttributionBoundary public

canonicalEisensteinDivisorPowerAttributionBoundary :
  EisensteinDivisorPowerAttributionBoundary
canonicalEisensteinDivisorPowerAttributionBoundary =
  eisenstein-divisor-power-attribution-boundary
    true true true true
    false false false
    "Serre and Miyake carry classical modular-form source context; A001158/A001160 are parity identifiers only; source presence, OEIS agreement, and finite-prefix agreement do not create proof, analytic convergence, or modular-form same-object authority"
