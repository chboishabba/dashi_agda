{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13RadiusSixWalkAgreementExact where

------------------------------------------------------------------------
-- PATH13 RADIUS-SIX WALK AGREEMENT
--
-- The centred radius-six block has side 13.  The direct centred-index map and
-- the repository periodic walk therefore live on the same literal finite
-- carrier.  This owner proves their equality directly instead of leaving the
-- existing decidable certificate as an uninhabited input.
--
-- Each centred coordinate contributes at most one straight signed segment.
-- At radius six there are exactly thirteen offset constructors.  The four
-- one-axis endpoint lemmas below reduce definitionally on those constructors;
-- the full four-dimensional theorem is then just sequential composition of
-- the four active segment lists.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredTorusBijectionExact as Bijection
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredEndpointCertificateExact as Endpoint
import DASHI.Physics.YangMills.BalabanPeriodicSegmentCommutationRound162Exact as R162
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192

Path13Index : Set
Path13Index = Carrier.CyclicIndex 13

path13SegmentAction :
  Contours.CommutingSegmentAction
    (Blocks.PeriodicBlock R192.path13PeriodicIndex)
    Contours.AxisSegment
path13SegmentAction =
  Embed.periodicSegmentAction
    (R162.periodicSegmentCommutation R192.path13PeriodicIndex)

followAppend :
  ∀ point left right →
  Contours.follow path13SegmentAction point (Contours._++_ left right)
  ≡ Contours.follow path13SegmentAction
      (Contours.follow path13SegmentAction point left) right
followAppend point [] right = refl
followAppend point (segment ∷ segments) right =
  followAppend (Contours.step path13SegmentAction point segment) segments right

axis0OffsetExact :
  ∀ (offset : Centered.CenteredOffset R158.sourceRadius)
    (c1 c2 c3 : Path13Index) →
  Contours.follow path13SegmentAction
    (Carrier.pair (Carrier.pair Carrier.zeroᵢ c1) (Carrier.pair c2 c3))
    (Contours.activeSegment Contours.axis0 (Embed.offsetToSignedCount offset))
  ≡ Carrier.pair
      (Carrier.pair (Bijection.centeredOffsetIndex offset) c1)
      (Carrier.pair c2 c3)
axis0OffsetExact Centered.centre c1 c2 c3 = refl
axis0OffsetExact (Centered.positive Carrier.zeroᵢ) c1 c2 c3 = refl
axis0OffsetExact (Centered.positive (Carrier.sucᵢ Carrier.zeroᵢ)) c1 c2 c3 = refl
axis0OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))) c1 c2 c3 = refl
axis0OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))) c1 c2 c3 = refl
axis0OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))))) c1 c2 c3 = refl
axis0OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))))) c1 c2 c3 = refl
axis0OffsetExact (Centered.negative Carrier.zeroᵢ) c1 c2 c3 = refl
axis0OffsetExact (Centered.negative (Carrier.sucᵢ Carrier.zeroᵢ)) c1 c2 c3 = refl
axis0OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))) c1 c2 c3 = refl
axis0OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))) c1 c2 c3 = refl
axis0OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))))) c1 c2 c3 = refl
axis0OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))))) c1 c2 c3 = refl

axis1OffsetExact :
  ∀ (offset : Centered.CenteredOffset R158.sourceRadius)
    (c0 c2 c3 : Path13Index) →
  Contours.follow path13SegmentAction
    (Carrier.pair (Carrier.pair c0 Carrier.zeroᵢ) (Carrier.pair c2 c3))
    (Contours.activeSegment Contours.axis1 (Embed.offsetToSignedCount offset))
  ≡ Carrier.pair
      (Carrier.pair c0 (Bijection.centeredOffsetIndex offset))
      (Carrier.pair c2 c3)
axis1OffsetExact Centered.centre c0 c2 c3 = refl
axis1OffsetExact (Centered.positive Carrier.zeroᵢ) c0 c2 c3 = refl
axis1OffsetExact (Centered.positive (Carrier.sucᵢ Carrier.zeroᵢ)) c0 c2 c3 = refl
axis1OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))) c0 c2 c3 = refl
axis1OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))) c0 c2 c3 = refl
axis1OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))))) c0 c2 c3 = refl
axis1OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))))) c0 c2 c3 = refl
axis1OffsetExact (Centered.negative Carrier.zeroᵢ) c0 c2 c3 = refl
axis1OffsetExact (Centered.negative (Carrier.sucᵢ Carrier.zeroᵢ)) c0 c2 c3 = refl
axis1OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))) c0 c2 c3 = refl
axis1OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))) c0 c2 c3 = refl
axis1OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))))) c0 c2 c3 = refl
axis1OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))))) c0 c2 c3 = refl

axis2OffsetExact :
  ∀ (offset : Centered.CenteredOffset R158.sourceRadius)
    (c0 c1 c3 : Path13Index) →
  Contours.follow path13SegmentAction
    (Carrier.pair (Carrier.pair c0 c1) (Carrier.pair Carrier.zeroᵢ c3))
    (Contours.activeSegment Contours.axis2 (Embed.offsetToSignedCount offset))
  ≡ Carrier.pair
      (Carrier.pair c0 c1)
      (Carrier.pair (Bijection.centeredOffsetIndex offset) c3)
axis2OffsetExact Centered.centre c0 c1 c3 = refl
axis2OffsetExact (Centered.positive Carrier.zeroᵢ) c0 c1 c3 = refl
axis2OffsetExact (Centered.positive (Carrier.sucᵢ Carrier.zeroᵢ)) c0 c1 c3 = refl
axis2OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))) c0 c1 c3 = refl
axis2OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))) c0 c1 c3 = refl
axis2OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))))) c0 c1 c3 = refl
axis2OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))))) c0 c1 c3 = refl
axis2OffsetExact (Centered.negative Carrier.zeroᵢ) c0 c1 c3 = refl
axis2OffsetExact (Centered.negative (Carrier.sucᵢ Carrier.zeroᵢ)) c0 c1 c3 = refl
axis2OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))) c0 c1 c3 = refl
axis2OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))) c0 c1 c3 = refl
axis2OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))))) c0 c1 c3 = refl
axis2OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))))) c0 c1 c3 = refl

axis3OffsetExact :
  ∀ (offset : Centered.CenteredOffset R158.sourceRadius)
    (c0 c1 c2 : Path13Index) →
  Contours.follow path13SegmentAction
    (Carrier.pair (Carrier.pair c0 c1) (Carrier.pair c2 Carrier.zeroᵢ))
    (Contours.activeSegment Contours.axis3 (Embed.offsetToSignedCount offset))
  ≡ Carrier.pair
      (Carrier.pair c0 c1)
      (Carrier.pair c2 (Bijection.centeredOffsetIndex offset))
axis3OffsetExact Centered.centre c0 c1 c2 = refl
axis3OffsetExact (Centered.positive Carrier.zeroᵢ) c0 c1 c2 = refl
axis3OffsetExact (Centered.positive (Carrier.sucᵢ Carrier.zeroᵢ)) c0 c1 c2 = refl
axis3OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))) c0 c1 c2 = refl
axis3OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))) c0 c1 c2 = refl
axis3OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))))) c0 c1 c2 = refl
axis3OffsetExact (Centered.positive (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))))) c0 c1 c2 = refl
axis3OffsetExact (Centered.negative Carrier.zeroᵢ) c0 c1 c2 = refl
axis3OffsetExact (Centered.negative (Carrier.sucᵢ Carrier.zeroᵢ)) c0 c1 c2 = refl
axis3OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))) c0 c1 c2 = refl
axis3OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))) c0 c1 c2 = refl
axis3OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))))) c0 c1 c2 = refl
axis3OffsetExact (Centered.negative (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)))))) c0 c1 c2 = refl

activeSegmentsEndpointExact :
  ∀ (point : Centered.CenteredBlockPoint4 R158.sourceRadius) →
  Contours.follow path13SegmentAction
    (Bijection.directCenteredOrigin {R158.sourceRadius})
    (Contours.activeSegments (Embed.centeredDisplacement4 point))
  ≡ Bijection.directCenteredEmbed point
activeSegmentsEndpointExact
    (Carrier.pair (Carrier.pair offset0 offset1)
      (Carrier.pair offset2 offset3)) =
  let
    i0 = Bijection.centeredOffsetIndex offset0
    i1 = Bijection.centeredOffsetIndex offset1
    i2 = Bijection.centeredOffsetIndex offset2

    s0 = Contours.activeSegment Contours.axis0 (Embed.offsetToSignedCount offset0)
    s1 = Contours.activeSegment Contours.axis1 (Embed.offsetToSignedCount offset1)
    s2 = Contours.activeSegment Contours.axis2 (Embed.offsetToSignedCount offset2)
    s3 = Contours.activeSegment Contours.axis3 (Embed.offsetToSignedCount offset3)

    after0 = Carrier.pair (Carrier.pair i0 Carrier.zeroᵢ)
      (Carrier.pair Carrier.zeroᵢ Carrier.zeroᵢ)
    after1 = Carrier.pair (Carrier.pair i0 i1)
      (Carrier.pair Carrier.zeroᵢ Carrier.zeroᵢ)
    after2 = Carrier.pair (Carrier.pair i0 i1)
      (Carrier.pair i2 Carrier.zeroᵢ)
  in
  trans
    (followAppend Bijection.directCenteredOrigin s0
      (Contours._++_ s1 (Contours._++_ s2 s3)))
    (trans
      (cong
        (λ start → Contours.follow path13SegmentAction start
          (Contours._++_ s1 (Contours._++_ s2 s3)))
        (axis0OffsetExact offset0 Carrier.zeroᵢ Carrier.zeroᵢ Carrier.zeroᵢ))
      (trans
        (followAppend after0 s1 (Contours._++_ s2 s3))
        (trans
          (cong
            (λ start → Contours.follow path13SegmentAction start
              (Contours._++_ s2 s3))
            (axis1OffsetExact offset1 i0 Carrier.zeroᵢ Carrier.zeroᵢ))
          (trans
            (followAppend after1 s2 s3)
            (trans
              (cong
                (λ start → Contours.follow path13SegmentAction start s3)
                (axis2OffsetExact offset2 i0 i1 Carrier.zeroᵢ))
              (axis3OffsetExact offset3 i0 i1 i2))))))

radiusSixDirectEmbeddingAgreesWithWalk :
  ∀ point → Bijection.directWalkAgreementPredicate
    {R158.sourceRadius} point
radiusSixDirectEmbeddingAgreesWithWalk point =
  trans
    (sym (activeSegmentsEndpointExact point))
    (Embed.followSegmentsEqualsWalkWord
      (R162.periodicSegmentCommutation R192.path13PeriodicIndex)
      Bijection.directCenteredOrigin
      (Contours.activeSegments (Embed.centeredDisplacement4 point)))

allFromPointwise :
  ∀ {A : Set} {Predicate : A → Set}
    (values : List A) →
  (∀ value → Predicate value) →
  Endpoint.All Predicate values
allFromPointwise [] pointwise = Endpoint.allNil
allFromPointwise (value ∷ values) pointwise =
  Endpoint.allCons (pointwise value) (allFromPointwise values pointwise)

radiusSixWalkAgreement :
  Bijection.CenteredTorusWalkAgreementCertificate R158.sourceRadius
radiusSixWalkAgreement = record
  { Bijection.CenteredTorusWalkAgreementCertificate.everyDirectEmbeddingAgreesWithWalk =
      allFromPointwise
        (Carrier.elements (Centered.centeredBlockFinite R158.sourceRadius))
        radiusSixDirectEmbeddingAgreesWithWalk
  }

path13RadiusSixWalkAgreementLevel : ProofLevel
path13RadiusSixWalkAgreementLevel = machineChecked

path13RadiusSixWalkAgreementConstructedLevel : ProofLevel
path13RadiusSixWalkAgreementConstructedLevel = machineChecked
