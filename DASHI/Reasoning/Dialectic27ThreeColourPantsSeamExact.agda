module DASHI.Reasoning.Dialectic27ThreeColourPantsSeamExact where

------------------------------------------------------------------------
-- EXACT TEST OF THE USER'S THREE-COLOUR RUBIK-CUBE/PANTS CONJECTURE.
--
-- A cube is the pre-existing X/Y dialectic -> Z interaction T³=27,
-- not three unrelated PNF/signed-evidence axes.
--
-- Its six outer faces each carry a NINE-SITE 3×3 colour field.
-- "Same colours" means equality of corresponding sites AFTER the
-- declared face-orientation identification, in a fixed named palette.
-- Colour equality is a NECESSARY part of this strict seam certificate.
-- It is NOT SUFFICIENT for canonical Pants.InterfaceMatch:
-- proposition, capacity, phase, wave and openness remain required.
--
-- Counterexample: identically painted faces, mismatched capacities.
-- Positive case: the *existing* selected-leg / inner-waist witness.
-- Allowed palette relabelling needs its own exact invertible chart;
-- numerical colour coincidence is not semantic identity.
-- Neither certificate creates new hyperfabric incidence nor a smooth
-- pair-of-pants or an independently mediated trialectic face.
--
-- Owners: TernaryComparisonSynthesisExact, XYInteractionZTransportExact,
-- Base369Ternary27HypervoxelFabricGeometryExact;
-- TypedHyperfabricPantsGluingBridgeExact and RelationalBranchCobordismGeometry;
-- original Base369 triadic symmetry; all prior proof credits retained.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Base369 as Base
import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Reasoning.DialecticXYInteractionZTransportExact as XY
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact as TypedPants
import DASHI.Reasoning.TrialecticGrothendieckTransitionCocycleExact as ExistingCocycle
import DASHI.Reasoning.TrialecticGrothendieckAttachedTwoCellDescentExact as ExistingTwoCell

-- Presentation palette is TAGGED; a colour is not automatically a
-- dialectical position, logical polarity, graph proper-colouring or proof.
data Paint3 : Set where
  red green blue : Paint3

paintToTri : Paint3 → Base.TriTruth
paintToTri red = Base.tri-low
paintToTri green = Base.tri-mid
paintToTri blue = Base.tri-high

triToPaint : Base.TriTruth → Paint3
triToPaint Base.tri-low = red
triToPaint Base.tri-mid = green
triToPaint Base.tri-high = blue

paintRoundTrip : (c : Paint3) → triToPaint (paintToTri c) ≡ c
paintRoundTrip red = refl
paintRoundTrip green = refl
paintRoundTrip blue = refl

-- A 3×3 face comprises two FREE coordinate axes of the same T³ cube.
FaceSite9 : Set
FaceSite9 = Trit.SSPTrit × Trit.SSPTrit

FaceColours : Set
FaceColours = FaceSite9 → Paint3

solid : Paint3 → FaceColours
solid c _ = c

-- The six opposed faces have matching coordinate types. A geometric
-- gluing identification also needs a chosen site alignment, here the
-- explicitly declared identity chart; twists/reflections are NOT implied.
data Opposed : Cube.Face6 → Cube.Face6 → Set where
  opposedX : Opposed Cube.xPositiveFace Cube.xNegativeFace
  opposedY : Opposed Cube.yPositiveFace Cube.yNegativeFace
  opposedZ : Opposed Cube.zPositiveFace Cube.zNegativeFace
  opposedXReverse : Opposed Cube.xNegativeFace Cube.xPositiveFace
  opposedYReverse : Opposed Cube.yNegativeFace Cube.yPositiveFace
  opposedZReverse : Opposed Cube.zNegativeFace Cube.zPositiveFace

record FacePatch : Set where
  constructor face-patch
  field
    side : Cube.Face6
    colours : FaceColours
    channel : Pants.BranchChannel
    sourceScope : String
open FacePatch public

-- The *strict*, fixed-palette/identity-site join rule. Using another
-- face-site orientation or colour chart requires an explicit isomorphism.
record FaceSeam (left right : FacePatch) : Set where
  constructor face-seam
  field
    opposedFaces : Opposed (side left) (side right)
    matchingColours : (u v : Trit.SSPTrit) →
      colours left (u , v) ≡ colours right (u , v)
    sameSourceScope : sourceScope left ≡ sourceScope right
    canonicalPantsInterface :
      Pants.InterfaceMatch (channel left) (channel right)
open FaceSeam public

-- The existing strict pants interface is a theorem-bearing condition:
-- identical paint does not automatically establish proposition agreement,
-- equal capacity/phase/wave, openness or semantic source alignment.
sameColourLeft : FacePatch
sameColourLeft = face-patch
  Cube.xPositiveFace (solid red)
  Pants.selectedChannel2
  "example:one-scope"

sameColourRightWrongCapacity : FacePatch
sameColourRightWrongCapacity = face-patch
  Cube.xNegativeFace (solid red)
  Pants.remainderChannel1
  "example:one-scope"

sameColourNineSites : (u v : Trit.SSPTrit) →
  colours sameColourLeft (u , v)
  ≡ colours sameColourRightWrongCapacity (u , v)
sameColourNineSites u v = refl

-- This counterexample is *exact*, because existing selectedChannel2
-- has capacity 2 but remainderChannel1 has capacity 1.
samePaintDoesNotProveCanonicalPantsSeam :
  FaceSeam sameColourLeft sameColourRightWrongCapacity → ⊥
samePaintDoesNotProveCanonicalPantsSeam gluing
  with Pants.capacityMatches (canonicalPantsInterface gluing)
... | ()

-- Reuse the pre-existing successful pants witness, not fabricated
-- equality of two arbitrary branch channels.
validLeft : FacePatch
validLeft = face-patch
  Cube.xPositiveFace (solid green)
  Pants.selectedChannel2
  "epbc:2019/8575:one-declared-interface"

validRight : FacePatch
validRight = face-patch
  Cube.xNegativeFace (solid green)
  Pants.innerInputChannel2
  "epbc:2019/8575:one-declared-interface"

validColourAndPantsSeam : FaceSeam validLeft validRight
validColourAndPantsSeam = face-seam
  opposedX
  (λ u v → refl)
  refl
  Pants.outerInnerMatch

positiveSeamUsesExistingExactPantsInterface :
  canonicalPantsInterface validColourAndPantsSeam
  ≡ Pants.outerInnerMatch
positiveSeamUsesExistingExactPantsInterface = refl

-- A change of palette CHART is different from changing the logical
-- predicate. A cyclic three-colour relabel has a canonical inverse.
-- It does not justify a join unless colour-chart alignment is declared.
rotatePaint : Paint3 → Paint3
rotatePaint c = triToPaint (Base.rotateTri (paintToTri c))

unrotatePaint : Paint3 → Paint3
unrotatePaint c = rotatePaint (rotatePaint c)

unrotateAfterRotate : (c : Paint3) →
  unrotatePaint (rotatePaint c) ≡ c
unrotateAfterRotate red = refl
unrotateAfterRotate green = refl
unrotateAfterRotate blue = refl

-- Red and green faces disagree under literal colour equality;
-- an invertible palette chart can match them without changing the
-- canonical pants-interface witness. This is a RELABELLED seam.
paletteLeft : FacePatch
paletteLeft = face-patch
  Cube.xPositiveFace (solid red)
  Pants.selectedChannel2
  "epbc:2019/8575:one-declared-interface"

paletteRight : FacePatch
paletteRight = face-patch
  Cube.xNegativeFace (solid green)
  Pants.innerInputChannel2
  "epbc:2019/8575:one-declared-interface"

literalRedNotGreen : red ≡ green → ⊥
literalRedNotGreen ()

paletteDoesNotMatchLiterally :
  FaceSeam paletteLeft paletteRight → ⊥
paletteDoesNotMatchLiterally gluing =
  literalRedNotGreen
    (matchingColours gluing Trit.sspZero Trit.sspZero)

record PaletteRechartedSeam
    (left right : FacePatch) : Set where
  constructor palette-recharted-seam
  field
    opposedFaces : Opposed (side left) (side right)
    chosenInvertibleRechart : (c : Paint3) →
      unrotatePaint (rotatePaint c) ≡ c
    rechartedColours : (u v : Trit.SSPTrit) →
      rotatePaint (colours left (u , v))
      ≡ colours right (u , v)
    sameSourceScope : sourceScope left ≡ sourceScope right
    canonicalPantsInterface :
      Pants.InterfaceMatch (channel left) (channel right)

paletteAgreementAfterDeclaredTransport :
  PaletteRechartedSeam paletteLeft paletteRight
paletteAgreementAfterDeclaredTransport =
  palette-recharted-seam
    opposedX
    unrotateAfterRotate
    (λ u v → refl)
    refl
    Pants.outerInnerMatch

------------------------------------------------------------------------
-- A THIRD joining constraint: pairwise matching observed face colours
-- does NOT automatically enforce coherence of a CYCLIC triple of
-- palette charts. The existing Grothendieck cocycle and attached face
-- are the actual formal owners for that higher-order obligation.
------------------------------------------------------------------------

swapGreenBlue : Paint3 → Paint3
swapGreenBlue red = red
swapGreenBlue green = blue
swapGreenBlue blue = green

swapGreenBlueInverse : (c : Paint3) →
  swapGreenBlue (swapGreenBlue c) ≡ c
swapGreenBlueInverse red = refl
swapGreenBlueInverse green = refl
swapGreenBlueInverse blue = refl

record ThreeFaceColourCycle : Set where
  constructor three-face-colour-cycle
  field
    patchAB patchBC patchCA : FaceColours
    chartAB chartBC chartCA : Paint3 → Paint3
    colourTransportAB : (u v : Trit.SSPTrit) →
      chartAB (patchAB (u , v)) ≡ patchBC (u , v)
    colourTransportBC : (u v : Trit.SSPTrit) →
      chartBC (patchBC (u , v)) ≡ patchCA (u , v)
    colourTransportCA : (u v : Trit.SSPTrit) →
      chartCA (patchCA (u , v)) ≡ patchAB (u , v)
open ThreeFaceColourCycle public

record PaletteCocycle (cycle : ThreeFaceColourCycle) : Set where
  constructor palette-cocycle
  field
    returnsEveryColour : (c : Paint3) →
      chartCA cycle (chartBC cycle (chartAB cycle c)) ≡ c
open PaletteCocycle public

-- All observed squares are RED. The AB chart swaps the UNUSED green
-- and blue sectors, keeping observed red fixed. Thus all three
-- pairwise patches match, but the global chart action is non-identity.
observedRedCycle : ThreeFaceColourCycle
observedRedCycle =
  three-face-colour-cycle
    (solid red) (solid red) (solid red)
    swapGreenBlue
    (λ c → c)
    (λ c → c)
    (λ u v → refl)
    (λ u v → refl)
    (λ u v → refl)

greenNotBlue : blue ≡ green → ⊥
greenNotBlue ()

pairwiseColourMatchesButChartCocycleFails :
  PaletteCocycle observedRedCycle → ⊥
pairwiseColourMatchesButChartCocycleFails cert =
  greenNotBlue (returnsEveryColour cert green)

-- All-red is STILL a fixed point: this counterexample rejects global
-- chart *equivariance on all colours*, NOT the existence of a particular
-- red-valued global section. The distinction is necessary.
redIsFixedEvenInBadCycle :
  chartCA observedRedCycle
    (chartBC observedRedCycle (chartAB observedRedCycle red))
  ≡ red
redIsFixedEvenInBadCycle = refl

-- The previously established C3 three-patch transport closure is
-- proof-relevant for its ORIGINAL CellDialectic chart action.
-- We do not substitute the above paint-cycle test for that theorem.
canonicalTrialecticCocycleOwner :
  ExistingCocycle.TrialecticGrothendieckTransitionCocycleBoundary
canonicalTrialecticCocycleOwner =
  ExistingCocycle.canonicalTrialecticGrothendieckTransitionCocycleBoundary

existingAttachedFaceOwner :
  ExistingTwoCell.TrialecticGrothendieckAttachedTwoCellBoundary
existingAttachedFaceOwner =
  ExistingTwoCell.canonicalTrialecticGrothendieckAttachedTwoCellBoundary

-- Ordinary paint agreement is just one of several orthogonal gates.
-- A successful seam certificate is NOT itself a new global section.
noNewFabricFromSeam :
  TypedPants.SeamCertificateAutomaticallyConstructsNewHyperfabric → ⊥
noNewFabricFromSeam =
  TypedPants.seamDoesNotAutomaticallyConstructNewHyperfabric

-- The 27-cube retains its actual typed dialectical coordinate semantics;
-- there are exactly nine face sites, not a new 3×3×3 face.
faceFreeAxisCount : Nat
faceFreeAxisCount = 3 * 3

faceFreeAxisCountIsNine : faceFreeAxisCount ≡ 9
faceFreeAxisCountIsNine = refl

xyRoleCubeCarrierIs27 :
  XY.carrierPositionCount ≡ 27
xyRoleCubeCarrierIs27 = XY.carrierPositionCountIs27
