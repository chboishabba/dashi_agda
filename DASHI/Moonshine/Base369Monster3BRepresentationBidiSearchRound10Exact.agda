module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound10Exact where

------------------------------------------------------------------------
-- ROUND 10: CHARACTER REGULAR C3 BULK -> LITERAL FIXED-SECTOR RESIDUAL
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

record Round10Status : Set where
  constructor round10Status
  field
    characterThreeBRestrictionCertified : Bool
    characterRegularC3Bulk196830 : Bool
    characterResidualFiftyThree : Bool
    literalThreePhaseFibresSameCentralAction : Bool
    literalZeta729Times90Recognition : Bool
    literalFixedRegular729Times90Recognition : Bool
    literalFixedResidual53Complement : Bool
    literalZetaSquaredRecognitionOrActualSwapTransport : Bool
    literalThreePhaseRegularBulk196830 : Bool
    literalSameActionResidual53 : Bool
    residual53AlbertRecognition : Bool
    seventyEightE6Recognition : Bool

canonicalRound10Status : Round10Status
canonicalRound10Status =
  round10Status
    true   -- certified CTblLib/character restriction authority
    true   -- 65610 Reg(C3) has dimension 196830
    true   -- +53 trivial-character residual
    true   -- all literal phase fibres come from the same central VOA action
    false  -- remains the same ActualZetaSectorRecognition scientific input
    false  -- NEW highest-alpha fixed-phase regular block recognition
    false  -- same-action complement producing the literal 53
    false  -- actual zeta<->zeta^2 transport/recognition still separate
    false  -- downstream of the three regular phase blocks
    false  -- downstream of fixed-sector split
    false  -- only after literal residual exists
    false  -- independent exceptional cross-check

------------------------------------------------------------------------
-- Search classification.
------------------------------------------------------------------------

data SearchClass : Set where
  OWNED GENERATED LIVE DOWNSTREAM PRUNED PARALLEL : SearchClass

characterC3DecompositionClass : SearchClass
characterC3DecompositionClass = OWNED

regularBulk196830CharacterClass : SearchClass
regularBulk196830CharacterClass = GENERATED

residual53CharacterClass : SearchClass
residual53CharacterClass = GENERATED

literalThreePhaseFamilyClass : SearchClass
literalThreePhaseFamilyClass = OWNED

zetaRecognitionClass : SearchClass
zetaRecognitionClass = LIVE

fixedRegularRecognitionClass : SearchClass
fixedRegularRecognitionClass = LIVE

fixedResidualComplementClass : SearchClass
fixedResidualComplementClass = LIVE

zetaSquaredTransportClass : SearchClass
zetaSquaredTransportClass = LIVE

literal196830BulkClass : SearchClass
literal196830BulkClass = DOWNSTREAM

literalResidual53Class : SearchClass
literalResidual53Class = DOWNSTREAM

albertResidualRecognitionClass : SearchClass
albertResidualRecognitionClass = DOWNSTREAM

seventyEightE6Class : SearchClass
seventyEightE6Class = PARALLEL

------------------------------------------------------------------------
-- The decisive new cut:
--
--   character:  W|C3 = 65610 Reg(C3) + 53*1       OWNED
--   states:     W_1 = RegularFixed_65610 + R_53   LIVE
--
-- Once the state-level fixed-sector split is recognized, R_53 is no longer a
-- dimension analogy.  It is a literal residual of the same selected 3B action.
------------------------------------------------------------------------
