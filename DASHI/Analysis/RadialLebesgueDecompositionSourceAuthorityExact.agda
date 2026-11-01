module DASHI.Analysis.RadialLebesgueDecompositionSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED SOURCE AUTHORITY: RADIAL LEBESGUE DECOMPOSITION
--
-- SOURCES
-- 1. R. B. Melrose, MIT 18.155 Lecture 9 (2013), equations (11)--(12):
--    R^n \ {0} is identified with (0,infinity) x S^{n-1}, and Lebesgue
--    measure has radial form r^{n-1} dr dω for the invariant sphere measure.
--    https://math.mit.edu/~rbm/18-155-F13/Lecture9.pdf
--
-- 2. MIT 18.01 polar-coordinate notes: a circle of radius r has circumference
--    2*pi*r, hence the invariant measure of S^1 is 2*pi.
--    https://math.mit.edu/~djk/18_01/chapter28/section03.html
--
-- This is theorem authority only.  It does not identify the source Lebesgue
-- measure, radial function, integrability hypotheses, or normalization with a
-- concrete DASHI/Casimir consumer.
------------------------------------------------------------------------

record RadialLebesgueDecompositionSourceAuthority : Set where
  field
    sourceName : String
    radialMeasureSourceLocator : String
    circleMeasureSourceLocator : String

    puncturedRnIdentifiedWithRadiusTimesSphere : Set
    lebesgueMeasureHasRnMinusOneRadialDensity : Set
    dimensionTwoRadialDensityIsRadius : Set
    unitCircleInvariantMeasureIsTwoPi : Set

    sourceBackedOnly : Set
    reading : String

open RadialLebesgueDecompositionSourceAuthority public

canonicalRadialLebesgueAuthority : RadialLebesgueDecompositionSourceAuthority
canonicalRadialLebesgueAuthority = record
  { sourceName =
      "MIT 18.155 Lecture 9 radial Lebesgue decomposition + MIT 18.01 circle measure"
  ; radialMeasureSourceLocator =
      "https://math.mit.edu/~rbm/18-155-F13/Lecture9.pdf"
  ; circleMeasureSourceLocator =
      "https://math.mit.edu/~djk/18_01/chapter28/section03.html"
  ; puncturedRnIdentifiedWithRadiusTimesSphere = ⊤
  ; lebesgueMeasureHasRnMinusOneRadialDensity = ⊤
  ; dimensionTwoRadialDensityIsRadius = ⊤
  ; unitCircleInvariantMeasureIsTwoPi = ⊤
  ; sourceBackedOnly = ⊤
  ; reading =
      "Source-backs the chart-free radial decomposition d^2k = r dr dω and the S^1 measure 2*pi; local radiality/integrability and same-measure identification remain application welds."
  }

data RadialSourceAutomaticallyIdentifiesCasimirMeasure : Set where

data RadialSourceAutomaticallyProvesCasimirIntegrability : Set where

sourceNeedsCasimirMeasureWeld :
  RadialSourceAutomaticallyIdentifiesCasimirMeasure → ⊥
sourceNeedsCasimirMeasureWeld ()

sourceDoesNotCreateIntegrability :
  RadialSourceAutomaticallyProvesCasimirIntegrability → ⊥
sourceDoesNotCreateIntegrability ()
