{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13CanonicalBondCenteredEmbeddingExact where

------------------------------------------------------------------------
-- PATH13: CANONICAL RADIUS-SIX EMBEDDING AT EVERY SIDE-13 SITE
--
-- The radius-six centred carrier has odd width 13.  The existing centred-torus
-- bijection gives an injective origin embedding once its finite walk-agreement
-- certificate is supplied.  This owner proves the missing opposite round trip
-- of that bijection, decodes an arbitrary side-13 site to its centred
-- coordinate, translates the origin embedding through the corresponding four
-- coordinate segments, and finally re-centres the record so its centre is
-- literally the requested site.
--
-- Consequently Eq. (119) does not need one independent no-wrap embedding per
-- coarse bond.  One radius-six walk-agreement certificate constructs them all.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredTorusBijectionExact as Bijection
import DASHI.Physics.YangMills.BalabanTranslatedCenteredEmbeddingRound163Exact as R163
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13

------------------------------------------------------------------------
-- Complete the finite centred-index bijection in the direction needed here.
------------------------------------------------------------------------

recombineSplit :
  ∀ {leftSize rightSize} →
  Bijection.IndexSplit leftSize rightSize →
  Carrier.CyclicIndex (leftSize + rightSize)
recombineSplit (Bijection.fromLeft index) =
  Bijection.injectLeftIndex index
recombineSplit (Bijection.fromRight index) =
  Bijection.injectRightIndex index

recombineSplitIndex :
  ∀ {leftSize rightSize}
    (index : Carrier.CyclicIndex (leftSize + rightSize)) →
  recombineSplit (Bijection.splitIndex {leftSize} {rightSize} index) ≡ index
recombineSplitIndex {zero} index = refl
recombineSplitIndex {suc leftSize} Carrier.zeroᵢ = refl
recombineSplitIndex {suc leftSize} {rightSize} (Carrier.sucᵢ index)
  with Bijection.splitIndex {leftSize} {rightSize} index
     | recombineSplitIndex {leftSize} {rightSize} index
... | Bijection.fromLeft left | equality = cong Carrier.sucᵢ equality
... | Bijection.fromRight right | equality = cong Carrier.sucᵢ equality

centeredOffsetEncodeDecode :
  ∀ {radius}
    (index : Carrier.CyclicIndex (suc (radius + radius))) →
  Bijection.centeredOffsetIndex
    (Bijection.centeredOffsetFromIndex index) ≡ index
centeredOffsetEncodeDecode Carrier.zeroᵢ = refl
centeredOffsetEncodeDecode {suc radius} (Carrier.sucᵢ index)
  with Bijection.splitIndex {suc radius} {suc radius} index
     | recombineSplitIndex {suc radius} {suc radius} index
... | Bijection.fromLeft left | equality = cong Carrier.sucᵢ equality
... | Bijection.fromRight right | equality
  rewrite Bijection.reverseFiniteIndexInvolutive right =
    cong Carrier.sucᵢ equality

pairCong :
  ∀ {A B : Set} {leftA rightA : A} {leftB rightB : B} →
  leftA ≡ rightA → leftB ≡ rightB →
  Carrier.pair leftA leftB ≡ Carrier.pair rightA rightB
pairCong refl refl = refl

directCenteredEncodeDecode :
  ∀ {radius}
    (site : Blocks.PeriodicBlock (Bijection.centeredTorusParameter radius)) →
  Bijection.directCenteredEmbed (Bijection.directCenteredDecode site) ≡ site
directCenteredEncodeDecode
    (Carrier.pair (Carrier.pair c0 c1) (Carrier.pair c2 c3)) =
  pairCong
    (pairCong
      (centeredOffsetEncodeDecode c0)
      (centeredOffsetEncodeDecode c1))
    (pairCong
      (centeredOffsetEncodeDecode c2)
      (centeredOffsetEncodeDecode c3))

------------------------------------------------------------------------
-- Translate the canonical origin embedding through a finite segment list.
------------------------------------------------------------------------

translateSegments :
  ∀ {n radius} →
  Embed.CenteredPeriodicNoWrapEmbedding n radius →
  List Contours.AxisSegment →
  Embed.CenteredPeriodicNoWrapEmbedding n radius
translateSegments embedding [] = embedding
translateSegments embedding (segment ∷ segments) =
  translateSegments (R163.translatedEmbedding embedding segment) segments

translateSegmentsCentre :
  ∀ {n radius}
    (embedding : Embed.CenteredPeriodicNoWrapEmbedding n radius)
    segments →
  Embed.embeddingCentre (translateSegments embedding segments)
  ≡ Bond.walk
      (Embed.embeddingCentre embedding)
      (Periodic.contourWord segments)
translateSegmentsCentre embedding [] = refl
translateSegmentsCentre embedding (segment ∷ segments) =
  trans
    (translateSegmentsCentre
      (R163.translatedEmbedding embedding segment) segments)
    (sym
      (Embed.walkAppend
        (Embed.embeddingCentre embedding)
        (Periodic.segmentWord segment)
        (Periodic.contourWord segments)))

------------------------------------------------------------------------
-- Radius-six / side-thirteen specialization.
------------------------------------------------------------------------

Path13Site : Set
Path13Site = Carrier.periodicTorus4Definition Side13.side13

radiusSixOriginEmbedding :
  Bijection.CenteredTorusWalkAgreementCertificate R158.sourceRadius →
  Embed.CenteredPeriodicNoWrapEmbedding
    R192.path13PeriodicIndex R158.sourceRadius
radiusSixOriginEmbedding certificate =
  Bijection.canonicalCenteredNoWrapEmbedding certificate

siteCenteredPoint :
  Path13Site → Centered.CenteredBlockPoint4 R158.sourceRadius
siteCenteredPoint = Bijection.directCenteredDecode

siteTranslationSegments : Path13Site → List Contours.AxisSegment
siteTranslationSegments site =
  Contours.activeSegments
    (Embed.centeredDisplacement4 (siteCenteredPoint site))

originWalkToSite :
  (certificate : Bijection.CenteredTorusWalkAgreementCertificate R158.sourceRadius) →
  ∀ site →
  Bond.walk
    (Embed.embeddingCentre (radiusSixOriginEmbedding certificate))
    (Periodic.contourWord (siteTranslationSegments site))
  ≡ site
originWalkToSite certificate site =
  trans
    (sym
      (Bijection.directEmbeddingAgreesWithWalk
        certificate (siteCenteredPoint site)))
    (directCenteredEncodeDecode site)

translatedEmbeddingAtSite :
  Bijection.CenteredTorusWalkAgreementCertificate R158.sourceRadius →
  Path13Site →
  Embed.CenteredPeriodicNoWrapEmbedding
    R192.path13PeriodicIndex R158.sourceRadius
translatedEmbeddingAtSite certificate site =
  translateSegments
    (radiusSixOriginEmbedding certificate)
    (siteTranslationSegments site)

translatedEmbeddingCentreIsSite :
  (certificate : Bijection.CenteredTorusWalkAgreementCertificate R158.sourceRadius) →
  ∀ site →
  Embed.embeddingCentre (translatedEmbeddingAtSite certificate site) ≡ site
translatedEmbeddingCentreIsSite certificate site =
  trans
    (translateSegmentsCentre
      (radiusSixOriginEmbedding certificate)
      (siteTranslationSegments site))
    (originWalkToSite certificate site)

recenterEmbedding :
  ∀ {n radius}
    (embedding : Embed.CenteredPeriodicNoWrapEmbedding n radius)
    (site : Blocks.PeriodicBlock n) →
  Embed.embeddingCentre embedding ≡ site →
  Embed.CenteredPeriodicNoWrapEmbedding n radius
recenterEmbedding embedding site centreExact = record
  { Embed.CenteredPeriodicNoWrapEmbedding.embeddingCentre = site
  ; Embed.CenteredPeriodicNoWrapEmbedding.embed = Embed.embed embedding
  ; Embed.CenteredPeriodicNoWrapEmbedding.embedMeaning = λ point →
      trans
        (Embed.embedMeaning embedding point)
        (cong (λ centre → Embed.centeredTargetSite centre point) centreExact)
  ; Embed.CenteredPeriodicNoWrapEmbedding.embedInjective =
      Embed.embedInjective embedding
  ; Embed.CenteredPeriodicNoWrapEmbedding.originMeaning =
      trans (Embed.originMeaning embedding) centreExact
  }

canonicalEmbeddingAtSite :
  Bijection.CenteredTorusWalkAgreementCertificate R158.sourceRadius →
  Path13Site →
  Embed.CenteredPeriodicNoWrapEmbedding
    R192.path13PeriodicIndex R158.sourceRadius
canonicalEmbeddingAtSite certificate site =
  recenterEmbedding
    (translatedEmbeddingAtSite certificate site)
    site
    (translatedEmbeddingCentreIsSite certificate site)

canonicalEmbeddingCentreExact :
  ∀ certificate site →
  Embed.embeddingCentre (canonicalEmbeddingAtSite certificate site) ≡ site
canonicalEmbeddingCentreExact certificate site = refl

canonicalEmbeddingInjective :
  ∀ certificate site {left right} →
  Embed.embed (canonicalEmbeddingAtSite certificate site) left
  ≡ Embed.embed (canonicalEmbeddingAtSite certificate site) right →
  left ≡ right
canonicalEmbeddingInjective certificate site =
  Embed.embedInjective (canonicalEmbeddingAtSite certificate site)

path13CanonicalBondCenteredEmbeddingLevel : ProofLevel
path13CanonicalBondCenteredEmbeddingLevel = machineChecked

path13PerBondEmbeddingReceiptPrunedLevel : ProofLevel
path13PerBondEmbeddingReceiptPrunedLevel = machineChecked

-- One finite source-scale certificate remains.  It replaces a family of
-- independently selectable per-bond embeddings.
literalPath13RadiusSixWalkAgreementCertificateLevel : ProofLevel
literalPath13RadiusSixWalkAgreementCertificateLevel = conditional
