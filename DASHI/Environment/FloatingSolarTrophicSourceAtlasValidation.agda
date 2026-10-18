module DASHI.Environment.FloatingSolarTrophicSourceAtlasValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Environment.FloatingSolarTrophicSourceAtlasExact as Sources

rayFulweilerDOIIsPinned :
  Sources.rayFulweiler2021DOI ≡ "10.1038/s41893-020-00644-9"
rayFulweilerDOIIsPinned = refl

chambersEtAlDOIIsPinned :
  Sources.chambersEtAl2024DOI ≡ "10.1016/j.aquaculture.2024.740540"
chambersEtAlDOIIsPinned = refl

imtaMeasuredNetNIsPinned : Sources.chambersReportedNetNRemovalKg ≡ "approximately 16.4 kg N"
imtaMeasuredNetNIsPinned = refl
