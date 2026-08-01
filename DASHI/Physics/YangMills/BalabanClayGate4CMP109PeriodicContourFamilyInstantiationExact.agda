module DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Adjacency
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicWordPathConstructionExact as WordPath
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours

------------------------------------------------------------------------
-- Literal periodic-path realization of the CMP109 contour permutations.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- The source contour algorithm first selects every nonzero coordinate
-- displacement, then follows its signed straight segment, and finally ranges
-- over every ordering of those segments.  The sibling module enumerates those
-- orderings.  Here each signed segment is expanded into the repository's
-- SignedAxis4 word and converted to a proof-bearing periodic nearest-neighbour
-- path.  The whole finite family is executable, with 24 members when all four
-- coordinates are active.  Only identification of the computed endpoint with
-- the selected CMP109 block endpoint remains physical.
------------------------------------------------------------------------

infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ right = right
(left ∷ lefts) ++ right = left ∷ (lefts ++ right)

axisToPeriodic : Contours.Axis4 → Carrier.Axis4
axisToPeriodic Contours.axis0 = Carrier.zeroᵢ
axisToPeriodic Contours.axis1 = Carrier.sucᵢ Carrier.zeroᵢ
axisToPeriodic Contours.axis2 =
  Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)
axisToPeriodic Contours.axis3 =
  Carrier.sucᵢ
    (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))

directionToOrientation : Contours.Direction → Bool
directionToOrientation Contours.positive = true
directionToOrientation Contours.negative = false

segmentSignedDirection : Contours.AxisSegment → Word.SignedAxis4
segmentSignedDirection segment =
  Carrier.pair
    (axisToPeriodic (Contours.axis segment))
    (directionToOrientation
      (Contours.direction (Contours.segmentCount segment)))

repeatDirection : Word.SignedAxis4 → Nat → List Word.SignedAxis4
repeatDirection direction zero = []
repeatDirection direction (suc count) =
  direction ∷ repeatDirection direction count

segmentWord : Contours.AxisSegment → List Word.SignedAxis4
segmentWord segment =
  repeatDirection
    (segmentSignedDirection segment)
    (Contours.count (Contours.segmentCount segment))

contourWord : List Contours.AxisSegment → List Word.SignedAxis4
contourWord [] = []
contourWord (segment ∷ segments) =
  segmentWord segment ++ contourWord segments

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

mapListLength :
  ∀ {A B : Set} (function : A → B) values →
  listLength (Contours.mapList function values) ≡ listLength values
mapListLength function [] = refl
mapListLength function (value ∷ values) =
  cong suc (mapListLength function values)

repeatDirectionLength : ∀ direction count →
  listLength (repeatDirection direction count) ≡ count
repeatDirectionLength direction zero = refl
repeatDirectionLength direction (suc count) =
  cong suc (repeatDirectionLength direction count)

segmentWordLength : ∀ segment →
  listLength (segmentWord segment)
  ≡ Contours.count (Contours.segmentCount segment)
segmentWordLength segment =
  repeatDirectionLength
    (segmentSignedDirection segment)
    (Contours.count (Contours.segmentCount segment))

periodicContourPath :
  ∀ {n}
    (start : Periodic.PeriodicBlock n)
    (order : List Contours.AxisSegment) →
  Adjacency.PeriodicPath start
    (Bond.walk start (contourWord order))
periodicContourPath start order =
  WordPath.wordToPeriodicPath start (contourWord order)

record ExecutablePeriodicContour
    (n : Nat)
    (start : Periodic.PeriodicBlock n) : Set where
  constructor executablePeriodicContour
  field
    order : List Contours.AxisSegment

  directions : List Word.SignedAxis4
  directions = contourWord order

  computedEndpoint : Periodic.PeriodicBlock n
  computedEndpoint = Bond.walk start directions

  path : Adjacency.PeriodicPath start computedEndpoint
  path = periodicContourPath start order

open ExecutablePeriodicContour public

makeExecutableContour :
  ∀ {n} (start : Periodic.PeriodicBlock n) →
  List Contours.AxisSegment → ExecutablePeriodicContour n start
makeExecutableContour start order = executablePeriodicContour order

allPeriodicContours :
  ∀ {n} (start : Periodic.PeriodicBlock n) →
  Contours.Displacement4 → List (ExecutablePeriodicContour n start)
allPeriodicContours start displacement =
  Contours.mapList (makeExecutableContour start)
    (Contours.cmp109ShortestContourOrders displacement)

allPeriodicContourCountEqualsOrderCount :
  ∀ {n} (start : Periodic.PeriodicBlock n) displacement →
  listLength (allPeriodicContours start displacement)
  ≡ listLength (Contours.cmp109ShortestContourOrders displacement)
allPeriodicContourCountEqualsOrderCount start displacement =
  mapListLength (makeExecutableContour start)
    (Contours.cmp109ShortestContourOrders displacement)

allPeriodicContourMembershipPreimage :
  ∀ {n} (start : Periodic.PeriodicBlock n) displacement contour →
  Contours._∈_ contour (allPeriodicContours start displacement) →
  Contours.MapPreimage
    (makeExecutableContour start)
    (Contours.cmp109ShortestContourOrders displacement)
    contour
allPeriodicContourMembershipPreimage start displacement contour membership =
  Contours.mapMembershipPreimage
    (makeExecutableContour start)
    (Contours.cmp109ShortestContourOrders displacement)
    contour membership

record PeriodicCMP109ContourFamily
    (n : Nat)
    (start : Periodic.PeriodicBlock n)
    (displacement : Contours.Displacement4) : Set where
  field
    selectedOrder : List Contours.AxisSegment
    selectedOrderEnumerated :
      Contours._∈_ selectedOrder
        (Contours.cmp109ShortestContourOrders displacement)

  executable : ExecutablePeriodicContour n start
  executable = makeExecutableContour start selectedOrder

open PeriodicCMP109ContourFamily public

record NamedPeriodicCMP109Contour
    (n : Nat)
    (start finish : Periodic.PeriodicBlock n)
    (displacement : Contours.Displacement4) : Set where
  field
    family : PeriodicCMP109ContourFamily n start displacement
    endpointExact : computedEndpoint (executable family) ≡ finish

  pathToNamedEndpoint : Adjacency.PeriodicPath start finish
  pathToNamedEndpoint =
    WordPath.wordToNamedEndpointPath
      start finish
      (directions (executable family))
      endpointExact

open NamedPeriodicCMP109Contour public

one : Nat
one = suc zero

allFourPositiveUnitDisplacement : Contours.Displacement4
allFourPositiveUnitDisplacement =
  Contours.displacement4
    (Contours.signedCount Contours.positive one)
    (Contours.signedCount Contours.positive one)
    (Contours.signedCount Contours.positive one)
    (Contours.signedCount Contours.positive one)

allFourPeriodicContourCount24 :
  ∀ {n} (start : Periodic.PeriodicBlock n) →
  listLength
    (allPeriodicContours start allFourPositiveUnitDisplacement)
  ≡ 24
allFourPeriodicContourCount24 start =
  trans
    (allPeriodicContourCountEqualsOrderCount
      start allFourPositiveUnitDisplacement)
    Contours.fourActiveContourFamilyHas24Members

cmp109SegmentToSignedWordLevel : ProofLevel
cmp109SegmentToSignedWordLevel = computed

cmp109SegmentWordLengthLevel : ProofLevel
cmp109SegmentWordLengthLevel = machineChecked

cmp109EnumeratedPeriodicPathConstructionLevel : ProofLevel
cmp109EnumeratedPeriodicPathConstructionLevel = machineChecked

cmp109FullPeriodicContourFamilyLevel : ProofLevel
cmp109FullPeriodicContourFamilyLevel = machineChecked

cmp109FourActivePeriodicContourCount24Level : ProofLevel
cmp109FourActivePeriodicContourCount24Level = machineChecked

cmp109NamedEndpointPathTransportLevel : ProofLevel
cmp109NamedEndpointPathTransportLevel = machineChecked

physicalCMP109ComputedEndpointIdentificationInputsLevel : ProofLevel
physicalCMP109ComputedEndpointIdentificationInputsLevel = conditional
