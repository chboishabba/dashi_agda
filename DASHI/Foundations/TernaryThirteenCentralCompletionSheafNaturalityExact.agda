module DASHI.Foundations.TernaryThirteenCentralCompletionSheafNaturalityExact where

------------------------------------------------------------------------
-- H2.02 original-site chart-change NATURALITY of full matching/glue:
-- stage atlas permutation sends compatible local families to
-- compatible families; restriction and the glued central coordinate
-- commute, and glued valuations commute pointwise.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.TernaryThirteenOriginalSourceRefinementExact as Ref
import DASHI.Foundations.TernaryThirteenCentralCompletionBundleSheafExact as Sheaf
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import Base369

refineLocalFamily :
  Sheaf.CentralLocalFamily → Sheaf.CentralLocalFamily
refineLocalFamily locals axis =
  locals (Ref.swapFirstTwo axis)

refineLocalFamilyCompatible :
  (locals : Sheaf.CentralLocalFamily) →
  Sheaf.centralFamilyCompatible locals →
  Sheaf.centralFamilyCompatible (refineLocalFamily locals)
refineLocalFamilyCompatible locals matching axis =
  trans
    (matching (Ref.swapFirstTwo axis))
    (sym (matching Atlas.atlas-1))

refineRestrictPointwise :
  (state : Rel.SourceCentralCompletionCarrier)
  (axis : Atlas.StageAtlasZeroToEleven) →
  Sheaf.restrictCentral (Ref.refineCentral state) axis
  ≡ refineLocalFamily (Sheaf.restrictCentral state) axis
refineRestrictPointwise state axis = refl

refineGlueValuationPointwise :
  (locals : Sheaf.CentralLocalFamily)
  (matching : Sheaf.centralFamilyCompatible locals)
  (axis : Atlas.StageAtlasZeroToEleven) →
  proj₁ (Sheaf.glueCentral
    (refineLocalFamily locals)
    (refineLocalFamilyCompatible locals matching)) axis
  ≡
  proj₁ (Ref.refineCentral
    (Sheaf.glueCentral locals matching)) axis
refineGlueValuationPointwise locals matching axis = refl

refineGlueCentre :
  (locals : Sheaf.CentralLocalFamily)
  (matching : Sheaf.centralFamilyCompatible locals) →
  proj₂ (Sheaf.glueCentral
    (refineLocalFamily locals)
    (refineLocalFamilyCompatible locals matching))
  ≡
  proj₂ (Ref.refineCentral (Sheaf.glueCentral locals matching))
refineGlueCentre locals matching =
  matching Atlas.atlas-1

refineMatchingPuncturePreservation :
  (locals : Sheaf.CentralLocalFamily)
  (matching : Sheaf.centralFamilyCompatible locals) →
  ¬ (proj₂ (Sheaf.glueCentral locals matching)
      ≡ Base369.tri-mid) →
  ¬ (proj₂ (Sheaf.glueCentral
      (refineLocalFamily locals)
      (refineLocalFamilyCompatible locals matching))
      ≡ Base369.tri-mid)
refineMatchingPuncturePreservation locals matching punctured neq =
  punctured (trans (sym (refineGlueCentre locals matching)) neq)
