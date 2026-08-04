module DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Adjacency
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicWordPathConstructionExact as WordPath
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered

------------------------------------------------------------------------
-- Embedding the literal centred block into the periodic fine lattice.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The displayed coordinates x-y = sum_mu n_mu e_mu with |n_mu| <= r are
-- converted to the exact Displacement4 carrier already used by the executable
-- all-permutations contour family.  The canonical target is not postulated: it
-- is the endpoint obtained by walking the canonical axis-ordered word.
--
-- To show that every printed permutation reaches that same periodic target one
-- needs only the elementary commutation of finite coordinate translations.  It
-- is isolated below as PeriodicSegmentCommutation; all word/path transport and
-- endpoint algebra is proved here.
------------------------------------------------------------------------

offsetToSignedCount :
  ∀ {radius} → Centered.CenteredOffset radius → Contours.SignedCount
offsetToSignedCount Centered.centre =
  Contours.signedCount Contours.positive zero
offsetToSignedCount (Centered.positive index) =
  Contours.signedCount Contours.positive
    (suc (Centered.centeredOffsetRank index))
offsetToSignedCount (Centered.negative index) =
  Contours.signedCount Contours.negative
    (suc (Centered.centeredOffsetRank index))

centeredDisplacement4 :
  ∀ {radius} → Centered.CenteredBlockPoint4 radius → Contours.Displacement4
centeredDisplacement4
    (Carrier.pair (Carrier.pair offset0 offset1)
      (Carrier.pair offset2 offset3)) =
  Contours.displacement4
    (offsetToSignedCount offset0)
    (offsetToSignedCount offset1)
    (offsetToSignedCount offset2)
    (offsetToSignedCount offset3)

canonicalCenteredContourWord :
  ∀ {radius} → Centered.CenteredBlockPoint4 radius →
  List Word.SignedAxis4
canonicalCenteredContourWord point =
  Periodic.contourWord
    (Contours.activeSegments (centeredDisplacement4 point))

centeredTargetSite :
  ∀ {n radius} →
  Blocks.PeriodicBlock n → Centered.CenteredBlockPoint4 radius →
  Blocks.PeriodicBlock n
centeredTargetSite start point =
  Bond.walk start (canonicalCenteredContourWord point)

centeredTargetPath :
  ∀ {n radius}
    (start : Blocks.PeriodicBlock n)
    (point : Centered.CenteredBlockPoint4 radius) →
  Adjacency.PeriodicPath start (centeredTargetSite start point)
centeredTargetPath start point =
  WordPath.wordToPeriodicPath start (canonicalCenteredContourWord point)

open import Data.List.Base using (_++_)

walkAppend :
  ∀ {n} (start : Blocks.PeriodicBlock n) left right →
  Bond.walk start (left ++ right)
  ≡ Bond.walk (Bond.walk start left) right
walkAppend start [] right = refl
walkAppend start (direction ∷ directions) right =
  walkAppend (Bond.walkStep start direction) directions right

record PeriodicSegmentCommutation (n : Nat) : Set₁ where
  field
    translationsCommute :
      ∀ (point : Blocks.PeriodicBlock n) left right →
      Bond.walk
        (Bond.walk point (Periodic.segmentWord left))
        (Periodic.segmentWord right)
      ≡
      Bond.walk
        (Bond.walk point (Periodic.segmentWord right))
        (Periodic.segmentWord left)

open PeriodicSegmentCommutation public

periodicSegmentAction :
  ∀ {n} → PeriodicSegmentCommutation n →
  Contours.CommutingSegmentAction
    (Blocks.PeriodicBlock n) Contours.AxisSegment
periodicSegmentAction {n} commutation = record
  { step =
      λ point segment → Bond.walk point (Periodic.segmentWord segment)
  ; distinctSegmentsCommute =
      translationsCommute {n} commutation
  }

followSegmentsEqualsWalkWord :
  ∀ {n}
    (commutation : PeriodicSegmentCommutation n)
    point segments →
  Contours.follow (periodicSegmentAction commutation) point segments
  ≡ Bond.walk point (Periodic.contourWord segments)
followSegmentsEqualsWalkWord commutation point [] = refl
followSegmentsEqualsWalkWord commutation point (segment ∷ segments) =
  trans
    (followSegmentsEqualsWalkWord commutation
      (Bond.walk point (Periodic.segmentWord segment)) segments)
    (sym
      (walkAppend point
        (Periodic.segmentWord segment)
        (Periodic.contourWord segments)))

enumeratedCenteredContourEndpointExact :
  ∀ {n radius}
    (commutation : PeriodicSegmentCommutation n)
    (start : Blocks.PeriodicBlock n)
    (point : Centered.CenteredBlockPoint4 radius)
    order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders
      (centeredDisplacement4 point)) →
  Bond.walk start (Periodic.contourWord order)
  ≡ centeredTargetSite start point
enumeratedCenteredContourEndpointExact commutation start point order membership =
  trans
    (sym (followSegmentsEqualsWalkWord commutation start order))
    (trans
      (Contours.cmp109EnumeratedContourEndpointExact
        (periodicSegmentAction commutation)
        (centeredDisplacement4 point)
        order membership start)
      (followSegmentsEqualsWalkWord commutation start
        (Contours.activeSegments (centeredDisplacement4 point))))

record CMP109CenteredPeriodicBlock
    (n radius : Nat) : Set₁ where
  field
    blockCentre : Blocks.PeriodicBlock n
    offsetPoint : Centered.CenteredBlockPoint4 radius

  targetSite : Blocks.PeriodicBlock n
  targetSite = centeredTargetSite blockCentre offsetPoint

  canonicalPath : Adjacency.PeriodicPath blockCentre targetSite
  canonicalPath = centeredTargetPath blockCentre offsetPoint

open CMP109CenteredPeriodicBlock public

cmp109CenteredDisplacementIdentificationLevel : ProofLevel
cmp109CenteredDisplacementIdentificationLevel = machineChecked

cmp109CenteredCanonicalPeriodicPathLevel : ProofLevel
cmp109CenteredCanonicalPeriodicPathLevel = machineChecked

cmp109CenteredAllPermutationEndpointReductionLevel : ProofLevel
cmp109CenteredAllPermutationEndpointReductionLevel = machineChecked

physicalPeriodicCoordinateTranslationCommutationInputsLevel : ProofLevel
physicalPeriodicCoordinateTranslationCommutationInputsLevel = conditional

physicalCMP109FineSpacingAndNoWrapInputsLevel : ProofLevel
physicalCMP109FineSpacingAndNoWrapInputsLevel = conditional

record CenteredPeriodicNoWrapEmbedding
    (n radius : Nat) : Set₁ where
  field
    embeddingCentre : Blocks.PeriodicBlock n
    embed : Centered.CenteredBlockPoint4 radius → Blocks.PeriodicBlock n

    embedMeaning : ∀ point →
      embed point ≡ centeredTargetSite embeddingCentre point

    embedInjective : ∀ {left right} →
      embed left ≡ embed right → left ≡ right

    originMeaning :
      embed Centered.centeredOrigin4 ≡ embeddingCentre

open CenteredPeriodicNoWrapEmbedding public

embeddedPrintedContourEndpointExact :
  ∀ {n radius}
    (commutation : PeriodicSegmentCommutation n)
    (embedding : CenteredPeriodicNoWrapEmbedding n radius)
    point order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders
      (centeredDisplacement4 point)) →
  Bond.walk (embeddingCentre embedding) (Periodic.contourWord order)
  ≡ embed embedding point
embeddedPrintedContourEndpointExact commutation embedding point order membership =
  trans
    (enumeratedCenteredContourEndpointExact
      commutation (embeddingCentre embedding) point order membership)
    (sym (embedMeaning embedding point))

cmp109CenteredNoWrapEmbeddingInterfaceLevel : ProofLevel
cmp109CenteredNoWrapEmbeddingInterfaceLevel = machineChecked
