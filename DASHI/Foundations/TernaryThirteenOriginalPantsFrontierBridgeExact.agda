module DASHI.Foundations.TernaryThirteenOriginalPantsFrontierBridgeExact where

------------------------------------------------------------------------
-- H2.02 / H1.01: ORIGINAL TernaryPantsFrontier path indexing for
-- the 12+1 source StageAtlas / Base369 valuation construction.
--
-- This is a same-carrier *finite address* bridge:
--     TritWord n <-> canonical PantsPath n
-- for arbitrary n, hence actual 13-path endpoints. The existing
-- Frontier owns the cylinder <-> pants equivalence and refinement.
-- This does NOT claim smooth cobordism, automatic Hyperfabric
-- InterfaceMatch, or independent relational/Monster semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Topology.TernaryCylinderPantsGeometryExact as Junction
import DASHI.Topology.TernaryPantsFrontierExact as Frontier
import DASHI.Geometry.SSP369Ultrametric as Cylinder
import DASHI.Foundations.TernaryThirteenFibreSplitExact as Word
import DASHI.Foundations.TernaryThirteenFibrePunctureExact as Puncture
import DASHI.Foundations.TernaryThirteenOriginalAxisValuationBridgeExact as Source
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import Base369 as Base

tritToSlot : Word.Trit → Junction.BranchSlot
tritToSlot Word.negative = Junction.slot3
tritToSlot Word.neutral = Junction.slot6
tritToSlot Word.positive = Junction.slot9

slotToTrit : Junction.BranchSlot → Word.Trit
slotToTrit Junction.slot3 = Word.negative
slotToTrit Junction.slot6 = Word.neutral
slotToTrit Junction.slot9 = Word.positive

tritSlotRoundTrip :
  (t : Word.Trit) → slotToTrit (tritToSlot t) ≡ t
tritSlotRoundTrip Word.negative = refl
tritSlotRoundTrip Word.neutral = refl
tritSlotRoundTrip Word.positive = refl

slotTritRoundTrip :
  (slot : Junction.BranchSlot) → tritToSlot (slotToTrit slot) ≡ slot
slotTritRoundTrip Junction.slot3 = refl
slotTritRoundTrip Junction.slot6 = refl
slotTritRoundTrip Junction.slot9 = refl

wordToPants :
  (n : Nat) → Word.TritWord n → Frontier.PantsPath n
wordToPants zero tt = vnil
wordToPants (suc n) (head , tail) =
  tritToSlot head vcons wordToPants n tail

pantsToWord :
  (n : Nat) → Frontier.PantsPath n → Word.TritWord n
pantsToWord zero vnil = tt
pantsToWord (suc n) (head vcons tail) =
  slotToTrit head , pantsToWord n tail

wordPantsRoundTrip :
  (n : Nat) (word : Word.TritWord n) →
  pantsToWord n (wordToPants n word) ≡ word
wordPantsRoundTrip zero tt = refl
wordPantsRoundTrip (suc n) (head , tail) =
  cong₂ _,_
    (tritSlotRoundTrip head)
    (wordPantsRoundTrip n tail)

pantsWordRoundTrip :
  (n : Nat) (path : Frontier.PantsPath n) →
  wordToPants n (pantsToWord n path) ≡ path
pantsWordRoundTrip zero vnil = refl
pantsWordRoundTrip (suc n) (head vcons tail) =
  cong₂ _vcons_
    (slotTritRoundTrip head)
    (pantsWordRoundTrip n tail)

-- The original ternary ultrametric address is the SAME finite
-- pants frontier represented with its three original digits.
wordToCylinder :
  (n : Nat) → Word.TritWord n → Cylinder.Address n
wordToCylinder n word =
  Frontier.pantsPathToAddress (wordToPants n word)

cylinderToWord :
  (n : Nat) → Cylinder.Address n → Word.TritWord n
cylinderToWord n address =
  pantsToWord n (Frontier.addressToPantsPath address)

wordCylinderRoundTrip :
  (n : Nat) (word : Word.TritWord n) →
  cylinderToWord n (wordToCylinder n word) ≡ word
wordCylinderRoundTrip n word =
  trans
    (cong (pantsToWord n)
      (Frontier.pantsPathAddressRoundTrip (wordToPants n word)))
    (wordPantsRoundTrip n word)

cylinderWordRoundTrip :
  (n : Nat) (address : Cylinder.Address n) →
  wordToCylinder n (cylinderToWord n address) ≡ address
cylinderWordRoundTrip n address =
  trans
    (cong Frontier.pantsPathToAddress
      (pantsWordRoundTrip n (Frontier.addressToPantsPath address)))
    (Frontier.addressPantsPathRoundTrip address)

-- The REAL original StageAtlas/tri-truth completion has a
-- concrete encoding into the existing depth-13 pants indexing.
sourceCentralToPants13 :
  Rel.SourceCentralCompletionCarrier → Frontier.PantsPath 13
sourceCentralToPants13 state =
  wordToPants 13 (Source.sourceCentralToThirteen state)

pants13ToSourceCentral :
  Frontier.PantsPath 13 → Rel.SourceCentralCompletionCarrier
pants13ToSourceCentral path =
  Source.thirteenToSourceCentral (pantsToWord 13 path)

pants13SourceRoundTrip :
  (path : Frontier.PantsPath 13) →
  sourceCentralToPants13 (pants13ToSourceCentral path) ≡ path
pants13SourceRoundTrip path =
  trans
    (cong (wordToPants 13)
      (Source.thirteenSourceRoundTrip (pantsToWord 13 path)))
    (pantsWordRoundTrip 13 path)

sourcePantsRoundTripOnAxis :
  (state : Rel.SourceCentralCompletionCarrier)
  (axis : Atlas.StageAtlasZeroToEleven) →
  proj₁ (pants13ToSourceCentral (sourceCentralToPants13 state)) axis
    ≡ proj₁ state axis
sourcePantsRoundTripOnAxis state axis
  rewrite wordPantsRoundTrip 13 (Source.sourceCentralToThirteen state) =
  Source.sourceCentralRoundTripOnAxis state axis

sourcePantsRoundTripOnCentre :
  (state : Rel.SourceCentralCompletionCarrier) →
  proj₂ (pants13ToSourceCentral (sourceCentralToPants13 state))
    ≡ proj₂ state
sourcePantsRoundTripOnCentre state
  rewrite wordPantsRoundTrip 13 (Source.sourceCentralToThirteen state) =
  Source.sourceCentralRoundTripOnCentre state

-- A chosen central neutral section is represented in the pants
-- path, but is not excluded from the unpunctured full frontier.
neutralSourcePantsEndsAtMiddleSlot :
  (valuation : Rel.SourceTwelveAxisValuation) →
  pantsToWord 13
    (sourceCentralToPants13 (Rel.sourceNeutralSection valuation))
  ≡ Puncture.centralCoordinateZeroSection
       (Source.valuationToWord valuation)
neutralSourcePantsEndsAtMiddleSlot valuation =
  trans
    (wordPantsRoundTrip 13
      (Source.sourceCentralToThirteen
        (Rel.sourceNeutralSection valuation)))
    (Source.sourceNeutralSectionCommutes valuation)

-- The 13th coordinate is a branch choice, not a puncture.
sourceCentralPantsCentreCanBeNeutral :
  (valuation : Rel.SourceTwelveAxisValuation) →
  proj₂ (pants13ToSourceCentral
    (sourceCentralToPants13 (Rel.sourceNeutralSection valuation)))
  ≡ Base.tri-mid
sourceCentralPantsCentreCanBeNeutral valuation =
  trans
    (sourcePantsRoundTripOnCentre
      (Rel.sourceNeutralSection valuation))
    refl
