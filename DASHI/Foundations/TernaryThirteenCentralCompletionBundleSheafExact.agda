module DASHI.Foundations.TernaryThirteenCentralCompletionBundleSheafExact where

------------------------------------------------------------------------
-- H2.02: ORIGINAL StageValuationBundleAtlas.BundleSheaf instance
-- on the original StageAtlasZeroToEleven and Base369.TriTruth
-- carriers, for the CONSTRUCTED 12+1 central completion.
--
-- Local data carries one local valuation AND its centre.
-- Compatible families agree on the centre at all 12 source
-- addresses. This requirement is substantive: independent local
-- centres do not glue to a single 13th coordinate.
--
-- This is a global-sections gluing construction on the actual
-- source stage carrier, NOT a claim about an independently
-- selected nontrivial Grothendieck topology or Monster module.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.StageValuationBundleAtlas as Bundle
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Site
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import Base369 as Base

CentralLocalSection : Set
CentralLocalSection = Base.TriTruth × Base.TriTruth

CentralLocalFamily : Set
CentralLocalFamily = Atlas.StageAtlasZeroToEleven → CentralLocalSection

centralFamilyCompatible : CentralLocalFamily → Set
centralFamilyCompatible locals =
  (axis : Atlas.StageAtlasZeroToEleven) →
  proj₂ (locals axis) ≡ proj₂ (locals Atlas.atlas-0)

restrictCentral :
  Rel.SourceCentralCompletionCarrier →
  Atlas.StageAtlasZeroToEleven →
  CentralLocalSection
restrictCentral (valuation , centre) axis =
  valuation axis , centre

glueCentral :
  (locals : CentralLocalFamily) →
  centralFamilyCompatible locals →
  Rel.SourceCentralCompletionCarrier
glueCentral locals compatibility =
  (λ axis → proj₁ (locals axis)) ,
  proj₂ (locals Atlas.atlas-0)

centralGlueRestricts :
  (locals : CentralLocalFamily)
  (compatibility : centralFamilyCompatible locals)
  (axis : Atlas.StageAtlasZeroToEleven) →
  restrictCentral (glueCentral locals compatibility) axis
  ≡ locals axis
centralGlueRestricts locals compatibility axis =
  cong₂ _,_ refl (sym (compatibility axis))

-- The original repository's exact BundleSheaf interface is inhabited
-- by genuine local data, an actual compatibility predicate and glue.
sourceCentralCompletionBundleSheaf :
  Bundle.BundleSheaf
    Atlas.StageAtlasZeroToEleven
    CentralLocalSection
    Rel.SourceCentralCompletionCarrier
sourceCentralCompletionBundleSheaf = record
  { restrict = restrictCentral
  ; compatible = centralFamilyCompatible
  ; glue = glueCentral
  ; glueRestricts = centralGlueRestricts
  }

-- Same stage site used by the StageTwelve owner; not a new
-- shadow category or invented notion of covering.
sourceCentralCompletionStageSheaf :
  Site.StageBundleSheaf
    CentralLocalSection
    Rel.SourceCentralCompletionCarrier
sourceCentralCompletionStageSheaf =
  sourceCentralCompletionBundleSheaf

-- Every global state yields a genuinely compatible local family.
centralRestrictsCompatible :
  (state : Rel.SourceCentralCompletionCarrier) →
  centralFamilyCompatible (restrictCentral state)
centralRestrictsCompatible state axis = refl

-- Constructed gluing recovers the source state by equality of
-- the selected centre and by POINTWISE equality of valuations.
-- No functional extensionality axiom.
centralGlueReturnsCentre :
  (state : Rel.SourceCentralCompletionCarrier) →
  proj₂ (glueCentral (restrictCentral state)
    (centralRestrictsCompatible state))
  ≡ proj₂ state
centralGlueReturnsCentre state = refl

centralGlueReturnsValuationPointwise :
  (state : Rel.SourceCentralCompletionCarrier)
  (axis : Atlas.StageAtlasZeroToEleven) →
  proj₁ (glueCentral (restrictCentral state)
    (centralRestrictsCompatible state)) axis
  ≡ proj₁ state axis
centralGlueReturnsValuationPointwise state axis = refl

-- The neutral coordinate cannot be absent from a full glued
-- carrier: it is a genuine global section. Puncturing it is an
-- additional restriction, never a theorem forced by 3^(12+1).
neutralSectionGluedCentre :
  (valuation : Rel.SourceTwelveAxisValuation) →
  proj₂ (glueCentral
    (restrictCentral (Rel.sourceNeutralSection valuation))
    (centralRestrictsCompatible
      (Rel.sourceNeutralSection valuation)))
  ≡ Base.tri-mid
neutralSectionGluedCentre valuation = refl

-- The central puncture is inherited *iff* the matched local
-- common centre is not neutral. Both directions are actual proofs.
centralPunctureGluingForward :
  (locals : CentralLocalFamily)
  (compatibility : centralFamilyCompatible locals) →
  ¬ (proj₂ (locals Atlas.atlas-0) ≡ Base.tri-mid) →
  ¬ (proj₂ (glueCentral locals compatibility) ≡ Base.tri-mid)
centralPunctureGluingForward locals compatibility neq = neq

centralPunctureGluingBackward :
  (locals : CentralLocalFamily)
  (compatibility : centralFamilyCompatible locals) →
  ¬ (proj₂ (glueCentral locals compatibility) ≡ Base.tri-mid) →
  ¬ (proj₂ (locals Atlas.atlas-0) ≡ Base.tri-mid)
centralPunctureGluingBackward locals compatibility neq = neq

-- Any nonzero local centre remains nonzero after gluing.
centralPunctureGluingAtEveryAxis :
  (locals : CentralLocalFamily)
  (compatible : centralFamilyCompatible locals) →
  ((axis : Atlas.StageAtlasZeroToEleven) →
    ¬ (proj₂ (locals axis) ≡ Base.tri-mid)) →
  ¬ (proj₂ (glueCentral locals compatible) ≡ Base.tri-mid)
centralPunctureGluingAtEveryAxis locals compatible localPunctured =
  localPunctured Atlas.atlas-0

-- Compatibility is necessary, not decorative: one contradictory
-- centre already falsifies the exact matching-family predicate.
badLocalFamily : CentralLocalFamily
badLocalFamily Atlas.atlas-0 = Base.tri-mid , Base.tri-mid
badLocalFamily Atlas.atlas-1 = Base.tri-mid , Base.tri-high
badLocalFamily _ = Base.tri-mid , Base.tri-mid

badLocalFamilyNotCompatible :
  centralFamilyCompatible badLocalFamily → ⊥
badLocalFamilyNotCompatible matching with matching Atlas.atlas-1
... | ()
