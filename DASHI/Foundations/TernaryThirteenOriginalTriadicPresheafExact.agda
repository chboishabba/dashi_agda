module DASHI.Foundations.TernaryThirteenOriginalTriadicPresheafExact where

------------------------------------------------------------------------
-- This is an ACTUAL contravariant restriction family on the already
-- existing seven-object A-B-C relational patch category. Restriction
-- along nonidentity morphisms is computed, and composition is proved.
-- It reuses the original Stage-12 category, including nontrivial
-- pullbacks, rather than defining new category machinery.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Foundations.TernaryThirteenOriginalTriadicSiteGluingExact as Triadic
import Base369 as Base

VertexSection : Set
VertexSection = Triadic.Block4 × Base.TriTruth

Section : Site.RelObj → Set
Section Site.globalABC = Triadic.GlobalTwelveCentre
Section Site.edgeAB = Triadic.PairChart
Section Site.edgeBC = Triadic.PairChart
Section Site.edgeCA = Triadic.PairChart
Section Site.vertexA = VertexSection
Section Site.vertexB = VertexSection
Section Site.vertexC = VertexSection

firstVertex : Triadic.PairChart → VertexSection
firstVertex p = Triadic.vertexBlock p , Triadic.chartCentre p

secondVertex : Triadic.PairChart → VertexSection
secondVertex p = Triadic.secondBlock p , Triadic.chartCentre p

-- Strict restrictions across all original nonidentity arrows.
restrictAlong :
  {U V : Site.RelObj} →
  Site.RelHom V U → Section U → Section V
restrictAlong (Site.idR _) value = value
restrictAlong Site.abToGlobal value = Triadic.restrictAB value
restrictAlong Site.bcToGlobal value = Triadic.restrictBC value
restrictAlong Site.caToGlobal value = Triadic.restrictCA value
restrictAlong Site.aToAB value = firstVertex value
restrictAlong Site.bToAB value = secondVertex value
restrictAlong Site.bToBC value = firstVertex value
restrictAlong Site.cToBC value = secondVertex value
restrictAlong Site.cToCA value = firstVertex value
restrictAlong Site.aToCA value = secondVertex value
restrictAlong Site.aToGlobal value =
  Triadic.globalA value , Triadic.globalCentre value
restrictAlong Site.bToGlobal value =
  Triadic.globalB value , Triadic.globalCentre value
restrictAlong Site.cToGlobal value =
  Triadic.globalC value , Triadic.globalCentre value

restrictIdentity :
  (U : Site.RelObj) (section : Section U) →
  restrictAlong (Site.idR U) section ≡ section
restrictIdentity U section = refl

-- Functoriality for every composable pair of source morphisms.
-- The only nonidentity two-step composites are A/B/C through AB,
-- BC or CA to the global object.
restrictComposition :
  {U V W : Site.RelObj}
  (f : Site.RelHom V W)
  (g : Site.RelHom U V)
  (section : Section W) →
  restrictAlong (Site.composeRel f g) section
  ≡ restrictAlong g (restrictAlong f section)
restrictComposition (Site.idR _) g section = refl
restrictComposition f (Site.idR _) section = refl
restrictComposition Site.abToGlobal Site.aToAB section = refl
restrictComposition Site.abToGlobal Site.bToAB section = refl
restrictComposition Site.bcToGlobal Site.bToBC section = refl
restrictComposition Site.bcToGlobal Site.cToBC section = refl
restrictComposition Site.caToGlobal Site.cToCA section = refl
restrictComposition Site.caToGlobal Site.aToCA section = refl

-- Three actual patch restrictions and six actual overlap
-- restrictions for the original distinguished covering sieve.
originalABSection :
  Triadic.GlobalTwelveCentre → Section Site.edgeAB
originalABSection = restrictAlong Site.abToGlobal

originalBCSection :
  Triadic.GlobalTwelveCentre → Section Site.edgeBC
originalBCSection = restrictAlong Site.bcToGlobal

originalCASection :
  Triadic.GlobalTwelveCentre → Section Site.edgeCA
originalCASection = restrictAlong Site.caToGlobal

aOverlapAgrees :
  (global : Triadic.GlobalTwelveCentre) →
  restrictAlong Site.aToAB (originalABSection global)
  ≡ restrictAlong Site.aToCA (originalCASection global)
aOverlapAgrees global = refl

bOverlapAgrees :
  (global : Triadic.GlobalTwelveCentre) →
  restrictAlong Site.bToAB (originalABSection global)
  ≡ restrictAlong Site.bToBC (originalBCSection global)
bOverlapAgrees global = refl

cOverlapAgrees :
  (global : Triadic.GlobalTwelveCentre) →
  restrictAlong Site.cToBC (originalBCSection global)
  ≡ restrictAlong Site.cToCA (originalCASection global)
cOverlapAgrees global = refl

-- Under the original selected A/B/C sieve, matching in this
-- presheaf is exactly the existing five-field TriadicMatching.
record CoverTripleMatches
  (ab : Section Site.edgeAB)
  (bc : Section Site.edgeBC)
  (ca : Section Site.edgeCA) : Set where
  constructor cover-triple-matches
  field
    sameA :
      restrictAlong Site.aToAB ab ≡ restrictAlong Site.aToCA ca
    sameB :
      restrictAlong Site.bToAB ab ≡ restrictAlong Site.bToBC bc
    sameC :
      restrictAlong Site.cToBC bc ≡ restrictAlong Site.cToCA ca
open CoverTripleMatches public

-- The original overlap pair equality includes BOTH its 4-axis
-- block and the centre, so two independent matching fields are
-- recovered by projections.
coverTripleToTriadicMatching :
  (ab : Section Site.edgeAB)
  (bc : Section Site.edgeBC)
  (ca : Section Site.edgeCA) →
  CoverTripleMatches ab bc ca →
  Triadic.TriadicMatching ab bc ca
coverTripleToTriadicMatching ab bc ca matched =
  Triadic.triadic-matching
    (cong proj₁ (sameB matched))
    (cong proj₁ (sameC matched))
    (cong proj₁ (sameA matched))
    (cong proj₂ (sameB matched))
    (cong proj₂ (sameC matched))

glueCoverTriple :
  (ab : Section Site.edgeAB)
  (bc : Section Site.edgeBC)
  (ca : Section Site.edgeCA) →
  CoverTripleMatches ab bc ca →
  Section Site.globalABC
glueCoverTriple ab bc ca matched =
  Triadic.glueTriadic ab bc ca
    (coverTripleToTriadicMatching ab bc ca matched)

glueCoverTripleAB :
  (ab : Section Site.edgeAB)
  (bc : Section Site.edgeBC)
  (ca : Section Site.edgeCA)
  (matched : CoverTripleMatches ab bc ca) →
  restrictAlong Site.abToGlobal
    (glueCoverTriple ab bc ca matched) ≡ ab
glueCoverTripleAB ab bc ca matched =
  Triadic.triadicABGlueRestricts ab bc ca
    (coverTripleToTriadicMatching ab bc ca matched)

glueCoverTripleBC :
  (ab : Section Site.edgeAB)
  (bc : Section Site.edgeBC)
  (ca : Section Site.edgeCA)
  (matched : CoverTripleMatches ab bc ca) →
  restrictAlong Site.bcToGlobal
    (glueCoverTriple ab bc ca matched) ≡ bc
glueCoverTripleBC ab bc ca matched =
  Triadic.triadicBCGlueRestricts ab bc ca
    (coverTripleToTriadicMatching ab bc ca matched)

glueCoverTripleCA :
  (ab : Section Site.edgeAB)
  (bc : Section Site.edgeBC)
  (ca : Section Site.edgeCA)
  (matched : CoverTripleMatches ab bc ca) →
  restrictAlong Site.caToGlobal
    (glueCoverTriple ab bc ca matched) ≡ ca
glueCoverTripleCA ab bc ca matched =
  Triadic.triadicCAGlueRestricts ab bc ca
    (coverTripleToTriadicMatching ab bc ca matched)
