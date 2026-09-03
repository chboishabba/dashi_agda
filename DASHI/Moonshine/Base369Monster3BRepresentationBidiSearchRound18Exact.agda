module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound18Exact where

open import Agda.Builtin.Bool using (Bool; false; true)

data SearchClass : Set where
  SOURCEBACKED OWNED GENERATED LIVE DOWNSTREAM REJECTED PARALLEL : SearchClass

record Round18Status : Set where
  constructor round18Status
  field
    WilsonTwelvePlusSeventyEightCharacterSplit : Bool
    Suz143IrreducibleSourceBacked : Bool
    G2FourMaximalInSuzSourceBacked : Bool
    G2FourOrdinary65Exists : Bool
    G2FourOrdinary78Exists : Bool
    arithmetic143Is65Plus78 : Bool
    actualSuz143RestrictionIs65Plus78 : Bool
    G2Four78IsSameAsWilson78 : Bool
    matchingDegreeAloneIdentifies78 : Bool
    Albert53StillHighestPriority : Bool
    subgroupAlbert53ProbeStillUseful : Bool

canonicalRound18Status : Round18Status
canonicalRound18Status =
  round18Status
    true  -- Wilson / CTblLib [12,78]
    true  -- Suz 143 source-backed irreducible
    true  -- G2(4) maximal in Suz
    true  -- ordinary degree 65 exists
    true  -- ordinary degree 78 exists
    true  -- 65 + 78 = 143
    false -- exact branching remains executable/live until GAP receipt
    false -- same-object 78 weld is a second theorem
    false -- dimension is insufficient
    false -- priority moves to G2(4)
    true  -- Albert probe retained as fallback/negative-control lane

wilsonSplitClass : SearchClass
wilsonSplitClass = OWNED

g2SourceClass : SearchClass
g2SourceClass = SOURCEBACKED

g2BranchingClass : SearchClass
g2BranchingClass = LIVE

sameSeventyEightClass : SearchClass
sameSeventyEightClass = DOWNSTREAM

albertPriorityClass : SearchClass
albertPriorityClass = PARALLEL

------------------------------------------------------------------------
-- Round-18 highest-alpha graph:
--
--      Suz 143  [SOURCE-BACKED irreducible]
--          |
--          | restrict to maximal G2(4)
--          v
--      65 + 78 ?                     [LIVE ordinary branching test]
--             \
--              78_G2
--                |
--                | same-object / cover-character weld
--                v
--              78_Wilson             [DOWNSTREAM]
--                |
--           12 + 78 = 90             [OWNED character-level split]
--                |
--       Completed10 x T^2            [GENERATED carrier chart]
--
-- The Albert 53 lane remains a subgroup-restriction fallback, not the primary
-- recognition target after the G2(4) lead.
------------------------------------------------------------------------
