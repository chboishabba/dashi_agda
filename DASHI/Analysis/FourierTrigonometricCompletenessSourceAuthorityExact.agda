module DASHI.Analysis.FourierTrigonometricCompletenessSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED SOURCE AUTHORITY FOR TRIGONOMETRIC L2 COMPLETENESS
--
-- SOURCE:
-- Encyclopedia of Mathematics, "Fourier series" / "Orthogonal series".
-- The trigonometric system is recorded as a closed/complete orthogonal system
-- in L2, with Parseval equality.  This is theorem authority only; it is not an
-- internal DASHI proof of TE/TM electromagnetic completeness.
------------------------------------------------------------------------

record FourierTrigonometricCompletenessSourceAuthority : Set where
  field
    sourceName : String
    sourceLocator : String
    trigonometricSystemClosedInL2 : Set
    parsevalIdentityAvailable : Set
    orthogonalCompletenessAvailable : Set
    sourceBackedOnly : Set
    reading : String

open FourierTrigonometricCompletenessSourceAuthority public

canonicalFourierCompletenessAuthority :
  FourierTrigonometricCompletenessSourceAuthority
canonicalFourierCompletenessAuthority = record
  { sourceName = "Encyclopedia of Mathematics: Fourier series / Orthogonal series"
  ; sourceLocator = "https://encyclopediaofmath.org/wiki/Fourier_series"
  ; trigonometricSystemClosedInL2 = ⊤
  ; parsevalIdentityAvailable = ⊤
  ; orthogonalCompletenessAvailable = ⊤
  ; sourceBackedOnly = ⊤
  ; reading = "Classical L2 trigonometric completeness is source-backed; transport to the exact perfect-conductor TE/TM Hilbert carrier remains a separate same-object theorem."
  }

data FourierSourceAutomaticallyProvesTETMCompleteness : Set where

fourierAuthorityDoesNotAutoCloseElectromagneticCompleteness :
  FourierSourceAutomaticallyProvesTETMCompleteness → ⊥
fourierAuthorityDoesNotAutoCloseElectromagneticCompleteness ()
