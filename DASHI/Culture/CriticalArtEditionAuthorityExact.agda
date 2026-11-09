module DASHI.Culture.CriticalArtEditionAuthorityExact where

------------------------------------------------------------------------
-- Original record ownership and attribution:
--   Australian Classification, Leon 1994 110 min, ID 00719356198E;
--   Gaumont, Leon version longue 1996 133 min;
--   Australian Classification / Netflix, Don't Look Up 2021 138 min;
--   Apple TV and Jeff Gibbs / Huron Mountain Films, Planet of
--   the Humans 2020 100 min.
-- Web-record locators live in the accompanying JSON manifest.
--
-- This is a FINITE SOURCE-INDEX carrier. Its constructor choices
-- are human transcriptions, not kernel authentications of web pages.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

data OriginalWork : Set where
  leon : OriginalWork
  dontLookUp : OriginalWork
  planetOfHumans : OriginalWork

data Edition : Set where
  leonAustralian1994 : Edition
  leonGaumontLong1996 : Edition
  dontLookUpAustralian2021 : Edition
  planetApple2020 : Edition

editionWork : Edition → OriginalWork
editionWork leonAustralian1994 = leon
editionWork leonGaumontLong1996 = leon
editionWork dontLookUpAustralian2021 = dontLookUp
editionWork planetApple2020 = planetOfHumans

advertisedDurationSeconds : Edition → Nat
advertisedDurationSeconds leonAustralian1994 = 6600
advertisedDurationSeconds leonGaumontLong1996 = 7980
advertisedDurationSeconds dontLookUpAustralian2021 = 8280
advertisedDurationSeconds planetApple2020 = 6000

leonAustralian110Minutes :
  advertisedDurationSeconds leonAustralian1994 ≡ 6600
leonAustralian110Minutes = refl

leonGaumont133Minutes :
  advertisedDurationSeconds leonGaumontLong1996 ≡ 7980
leonGaumont133Minutes = refl

twoLeonCutsNotSameEdition :
  leonAustralian1994 ≡ leonGaumontLong1996 → ⊥
twoLeonCutsNotSameEdition ()

bothLeonEditionsSameWork :
  editionWork leonAustralian1994 ≡ editionWork leonGaumontLong1996
bothLeonEditionsSameWork = refl

data SourceGrade : Set where
  bibliographicAuthority : SourceGrade
  originalSceneVerified : SourceGrade
  responseEmpiricallyMeasured : SourceGrade

editionGrade : Edition → SourceGrade
editionGrade _ = bibliographicAuthority

sourceMetadataNotVerifiedScene :
  (edition : Edition) →
  editionGrade edition ≡ originalSceneVerified → ⊥
sourceMetadataNotVerifiedScene leonAustralian1994 ()
sourceMetadataNotVerifiedScene leonGaumontLong1996 ()
sourceMetadataNotVerifiedScene dontLookUpAustralian2021 ()
sourceMetadataNotVerifiedScene planetApple2020 ()

sourceMetadataNotMeasuredAudience :
  (edition : Edition) →
  editionGrade edition ≡ responseEmpiricallyMeasured → ⊥
sourceMetadataNotMeasuredAudience leonAustralian1994 ()
sourceMetadataNotMeasuredAudience leonGaumontLong1996 ()
sourceMetadataNotMeasuredAudience dontLookUpAustralian2021 ()
sourceMetadataNotMeasuredAudience planetApple2020 ()

-- Original source review is a separate required gate. Even a confirmed
-- original edition duration supplies no frame, dialogue or viewer claim.
