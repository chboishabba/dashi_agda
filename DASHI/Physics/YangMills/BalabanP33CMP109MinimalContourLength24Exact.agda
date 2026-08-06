module DASHI.Physics.YangMills.BalabanP33CMP109MinimalContourLength24Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - I. Small Fields",
-- arXiv:1108.1335v2 [math-ph]. No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- Close the conditional coordinate-displacement leaf in the repository's
-- minimal source-admissible CMP109 geometry.  The scale has radius r=6 and
-- centred coordinates in {-6,...,6}.  Every shortest coordinate contour has
-- length
--
--   |delta_0| + |delta_1| + |delta_2| + |delta_3| <= 4 r = 24.
--
-- The proof is on the literal bounded centred-offset carrier.  It then rewrites
-- through the existing exact contour-length theorem, so every permutation in
-- G(y,x), not merely one selected path, inherits the numerical bound 24.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ContourLengthExact as Length
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal

cyclicRankSuccessorBound :
  ∀ {radius} (index : Carrier.CyclicIndex radius) →
  suc (Centered.centeredOffsetRank index) ≤ radius
cyclicRankSuccessorBound {suc radius} Carrier.zeroᵢ = s≤s z≤n
cyclicRankSuccessorBound {suc radius} (Carrier.sucᵢ index) =
  s≤s (cyclicRankSuccessorBound index)

centeredOffsetMagnitudeBound :
  ∀ {radius} (offset : Centered.CenteredOffset radius) →
  Centered.centeredOffsetMagnitude offset ≤ radius
centeredOffsetMagnitudeBound Centered.centre = z≤n
centeredOffsetMagnitudeBound (Centered.positive index) =
  cyclicRankSuccessorBound index
centeredOffsetMagnitudeBound (Centered.negative index) =
  cyclicRankSuccessorBound index

centeredOffsetSignedCount :
  ∀ {radius} →
  Centered.CenteredOffset radius → Contours.SignedCount
centeredOffsetSignedCount Centered.centre =
  Contours.signedCount Contours.positive zero
centeredOffsetSignedCount (Centered.positive index) =
  Contours.signedCount Contours.positive
    (suc (Centered.centeredOffsetRank index))
centeredOffsetSignedCount (Centered.negative index) =
  Contours.signedCount Contours.negative
    (suc (Centered.centeredOffsetRank index))

centeredPointDisplacement :
  ∀ {radius} →
  Centered.CenteredBlockPoint4 radius → Contours.Displacement4
centeredPointDisplacement
    (Carrier.pair (Carrier.pair offset0 offset1)
      (Carrier.pair offset2 offset3)) =
  Contours.displacement4
    (centeredOffsetSignedCount offset0)
    (centeredOffsetSignedCount offset1)
    (centeredOffsetSignedCount offset2)
    (centeredOffsetSignedCount offset3)

addNatRightZero : ∀ value → Length.addNat value zero ≡ value
addNatRightZero zero = refl
addNatRightZero (suc value) = cong suc (addNatRightZero value)

segmentCountSumAppend : ∀ left right →
  Length.segmentCountSum (Contours._++_ left right)
  ≡ Length.addNat
      (Length.segmentCountSum left)
      (Length.segmentCountSum right)
segmentCountSumAppend [] right = refl
segmentCountSumAppend (segment ∷ segments) right =
  trans
    (cong
      (Length.addNat
        (Contours.count (Contours.segmentCount segment)))
      (segmentCountSumAppend segments right))
    (sym
      (Length.addNatAssociative
        (Contours.count (Contours.segmentCount segment))
        (Length.segmentCountSum segments)
        (Length.segmentCountSum right)))

activeSegmentCountExact : ∀ axis signed →
  Length.segmentCountSum (Contours.activeSegment axis signed)
  ≡ Contours.count signed
activeSegmentCountExact axis (Contours.signedCount direction zero) = refl
activeSegmentCountExact axis
    (Contours.signedCount direction (suc count)) =
  addNatRightZero (suc count)

activeSegmentsCountExact : ∀ displacement →
  Length.segmentCountSum (Contours.activeSegments displacement)
  ≡ Length.addNat (Contours.count (Contours.coordinate0 displacement))
      (Length.addNat (Contours.count (Contours.coordinate1 displacement))
        (Length.addNat (Contours.count (Contours.coordinate2 displacement))
          (Contours.count (Contours.coordinate3 displacement))))
activeSegmentsCountExact displacement
  rewrite segmentCountSumAppend
    (Contours.activeSegment Contours.axis0
      (Contours.coordinate0 displacement))
    (Contours._++_
      (Contours.activeSegment Contours.axis1
        (Contours.coordinate1 displacement))
      (Contours._++_
        (Contours.activeSegment Contours.axis2
          (Contours.coordinate2 displacement))
        (Contours.activeSegment Contours.axis3
          (Contours.coordinate3 displacement))))
  | segmentCountSumAppend
      (Contours.activeSegment Contours.axis1
        (Contours.coordinate1 displacement))
      (Contours._++_
        (Contours.activeSegment Contours.axis2
          (Contours.coordinate2 displacement))
        (Contours.activeSegment Contours.axis3
          (Contours.coordinate3 displacement)))
  | segmentCountSumAppend
      (Contours.activeSegment Contours.axis2
        (Contours.coordinate2 displacement))
      (Contours.activeSegment Contours.axis3
        (Contours.coordinate3 displacement))
  | activeSegmentCountExact Contours.axis0
      (Contours.coordinate0 displacement)
  | activeSegmentCountExact Contours.axis1
      (Contours.coordinate1 displacement)
  | activeSegmentCountExact Contours.axis2
      (Contours.coordinate2 displacement)
  | activeSegmentCountExact Contours.axis3
      (Contours.coordinate3 displacement) = refl

centeredPointCountSumBound :
  ∀ {radius} (point : Centered.CenteredBlockPoint4 radius) →
  Length.segmentCountSum
    (Contours.activeSegments (centeredPointDisplacement point))
  ≤ Length.addNat radius
      (Length.addNat radius (Length.addNat radius radius))
centeredPointCountSumBound
    point@(Carrier.pair (Carrier.pair offset0 offset1)
      (Carrier.pair offset2 offset3)) =
  subst
    (λ selected →
      selected
      ≤ Length.addNat _ (Length.addNat _ (Length.addNat _ _)))
    (sym (activeSegmentsCountExact (centeredPointDisplacement point)))
    (NatP.+-mono-≤
      (centeredOffsetMagnitudeBound offset0)
      (NatP.+-mono-≤
        (centeredOffsetMagnitudeBound offset1)
        (NatP.+-mono-≤
          (centeredOffsetMagnitudeBound offset2)
          (centeredOffsetMagnitudeBound offset3))))

minimalFourRadiusIsTwentyFour :
  Length.addNat Minimal.radius
    (Length.addNat Minimal.radius
      (Length.addNat Minimal.radius Minimal.radius))
  ≡ 24
minimalFourRadiusIsTwentyFour = refl

minimalCenteredContourLengthAtMost24 :
  (point : Centered.CenteredBlockPoint4 Minimal.radius) →
  ∀ order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders
      (centeredPointDisplacement point)) →
  Periodic.listLength (Periodic.contourWord order) ≤ 24
minimalCenteredContourLengthAtMost24 point order membership =
  subst
    (λ upper →
      Periodic.listLength (Periodic.contourWord order) ≤ upper)
    minimalFourRadiusIsTwentyFour
    (subst
      (λ selected → selected
        ≤ Length.addNat Minimal.radius
            (Length.addNat Minimal.radius
              (Length.addNat Minimal.radius Minimal.radius)))
      (sym
        (Length.enumeratedContourWordLengthExact
          (centeredPointDisplacement point) order membership))
      (centeredPointCountSumBound point))

cmp109CenteredOffsetMagnitudeBoundLevel : ProofLevel
cmp109CenteredOffsetMagnitudeBoundLevel = machineChecked

cmp109MinimalContourLength24Level : ProofLevel
cmp109MinimalContourLength24Level = machineChecked
