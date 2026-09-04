module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound19Exact where

open import Agda.Builtin.Bool using (Bool; false; true)

data SearchClass : Set where
  SOURCEBACKED OWNED GENERATED LIVE DOWNSTREAM REJECTED : SearchClass

record Round19Status : Set where
  constructor round19Status
  field
    g2FourMaximalInSuz : Bool
    threeTimesG2FourInThreeSuz : Bool
    threeTimesTwoG2FourInSixSuz : Bool
    g2FourOrdinary65And78 : Bool
    arithmetic65Plus78Equals143 : Bool
    suz143RestrictionExact65Plus78 : Bool
    threeSuz78RestrictionComputed : Bool
    sixSuz12RestrictionComputed : Bool
    WilsonTwelvePlusSeventyEightCharacterSplit : Bool
    sameDegree78ImpliesSameObject : Bool
    sharedG2Four78ClassFunctionWeld : Bool
    coverCoherentTwelveSeventyEight143Triangle : Bool
    AlbertFiftyThreeHighestPriority : Bool

canonicalRound19Status : Round19Status
canonicalRound19Status =
  round19Status
    true true true
    true true
    false false false
    true
    false false false
    false

g2FourSuzClass : SearchClass
g2FourSuzClass = SOURCEBACKED

coverSpineClass : SearchClass
coverSpineClass = SOURCEBACKED

sixtyFiveSeventyEightDegreeClass : SearchClass
sixtyFiveSeventyEightDegreeClass = SOURCEBACKED

suz143BranchClass : SearchClass
suz143BranchClass = LIVE

threeSuz78RestrictionClass : SearchClass
threeSuz78RestrictionClass = LIVE

sixSuz12RestrictionClass : SearchClass
sixSuz12RestrictionClass = LIVE

wilsonTwelveSeventyEightClass : SearchClass
wilsonTwelveSeventyEightClass = OWNED

sameDegreePromotesClass : SearchClass
sameDegreePromotesClass = REJECTED

sharedSeventyEightWeldClass : SearchClass
sharedSeventyEightWeldClass = DOWNSTREAM

coverTriangleClass : SearchClass
coverTriangleClass = DOWNSTREAM

albertPriorityClass : SearchClass
albertPriorityClass = DOWNSTREAM

------------------------------------------------------------------------
-- Round-19 target:
--
--   Suz_143 | G2(4) ?= 65 + 78
--                          |
--                          | same restricted class function / action?
--                          v
--   3.Suz_78 | 3xG2(4) -> Wilson multiplicity 78
--
--   6.Suz_12 | 3x2.G2(4)
--
-- together with Wilson's already-owned 12 + 78 = 90 character split.
--
-- Only after these restrictions are computed may one assert a single
-- cover-coherent G2(4) spine joining the fixed 143 and nontrivial-phase 90.
------------------------------------------------------------------------
