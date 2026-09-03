module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound17Exact where

------------------------------------------------------------------------
-- ROUND 17: WILSON 1988 RESTRICTION + 143-DOWNARROW-H TEST FRONTIER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

data SearchClass : Set where
  OWNED SOURCEBACKED GENERATED LIVE DOWNSTREAM PRUNED REJECTED : SearchClass

record Round17Status : Set where
  constructor round17Status
  field
    wilson196883RestrictionPattern : Bool
    fixedNormalizer65520Plus143 : Bool
    pairedPhase729PairTimesTwelvePlusSeventyEight : Bool
    twelvePlusSeventyEightCharacterLevel : Bool
    twelvePlusSeventyEightLiteralFin90BlockIntertwiner : Bool
    completed10TimesT2CrossChartAfterBlockWeld : Bool
    centralC3Balanced65610Plus53 : Bool
    suzStable143SplitsAs90Plus53 : Bool
    fullNormalizerStableResidual53 : Bool
    ninetyObserverTransferArithmetic : Bool
    suz143SubgroupRestrictionProbeImplemented : Bool
    subgroupInvariant53Detection : Bool
    albertRecognitionPromoted : Bool

canonicalRound17Status : Round17Status
canonicalRound17Status =
  round17Status
    true   -- Wilson 1988 source-backed restriction pattern
    true   -- 65520 + 143 fixed/centre-trivial contribution
    true   -- paired nonlinear extraspecial phases
    true   -- existing CTblLib producer certifies multiplicity degrees [12,78]
    false  -- still need literal Fin90 same-action block realization
    true   -- generated after that block realization
    true   -- exact central-C3 character balancing
    false  -- impossible at full Suz level because 143 is irreducible
    false  -- therefore do not claim an N(3B)-stable R53
    true   -- 65610=65520+90 and 143=90+53
    true   -- GAP/CTblLib probe added for selected maximal subgroups
    false  -- requires actual probe output/receipt
    false  -- downstream only if a subgroup restriction supports it

wilsonRestrictionClass : SearchClass
wilsonRestrictionClass = SOURCEBACKED

fixed65520Plus143Class : SearchClass
fixed65520Plus143Class = SOURCEBACKED

twelvePlusSeventyEightCharacterClass : SearchClass
twelvePlusSeventyEightCharacterClass = OWNED

twelvePlusSeventyEightLiteralActionClass : SearchClass
twelvePlusSeventyEightLiteralActionClass = LIVE

centralResidual53Class : SearchClass
centralResidual53Class = OWNED

fullNormalizerResidual53Class : SearchClass
fullNormalizerResidual53Class = REJECTED

suz143NinetyPlusFiftyThreeClass : SearchClass
suz143NinetyPlusFiftyThreeClass = REJECTED

subgroupRestrictionProbeClass : SearchClass
subgroupRestrictionProbeClass = LIVE

albertRecognitionClass : SearchClass
albertRecognitionClass = DOWNSTREAM

------------------------------------------------------------------------
-- Decisive Round-17 firewall:
--
-- Published normalizer observer:
--   196883 = 143 + 65520 + (729+729')*(12+78).
--
-- Central-C3 observer:
--   196883 = 53 + 3*65610.
--
-- Reconciliation arithmetic:
--   65610 = 65520 + 90,
--   143   = 90 + 53.
--
-- The transfer 90 is not a Suz-stable submodule extraction.  Any actual 53
-- module must arise only after restriction to a named smaller actor H, and the
-- GAP probe must exhibit an invariant 53-dimensional sub-sum before the Albert
-- lane can be promoted.
------------------------------------------------------------------------
