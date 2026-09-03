module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound16Exact where

------------------------------------------------------------------------
-- ROUND 16: GLOBAL 9 = 1 + 2 + 6 / FIXED-PHASE CORRECTION
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

data SearchClass : Set where
  OWNED GENERATED LIVE DOWNSTREAM PRUNED PARALLEL CORRECTED : SearchClass

record Round16Status : Set where
  constructor round16Status
  field
    base369Primary196830TenTimesThreeToNine : Bool
    certifiedC3RegularBulkThreeTimes65610 : Bool
    exponentNineSplitsOnePlusTwoPlusSix : Bool
    fin90ToCompleted10TimesT2 : Bool
    actualMultiplicityActionTransportedToProduct : Bool
    separateNinetyRecognitionPayment : Bool
    productActionFactorisation : Bool
    productActionCouplingTest : Bool
    twelvePlusSeventyEightActualBlockSplit : Bool
    productVsTwelveSeventyEightCrossChart : Bool
    zeta729Times90Recognition : Bool
    zetaSquaredTransportOrRecognition : Bool
    fixedPhase729Times90StoneVonNeumannTarget : Bool
    fixedPhaseAbelianQuotientTarget : Bool
    fixedPhase65610QuotientCharacterBlock : Bool
    literalResidual53 : Bool
    residualAlbertRecognition : Bool

canonicalRound16Status : Round16Status
canonicalRound16Status =
  round16Status
    true   -- original 10 * 3^9 primary
    true   -- certified character-level 3 * 65610
    true   -- 3^9 = 3 * 3^2 * 3^6
    true   -- compiler output
    true   -- after actual inertia attachment, transport is by construction
    false  -- pruned as independent scientific payment
    false  -- genuinely live: does action split coordinatewise?
    true   -- exact negative witnesses are available if coupling is found
    false  -- actual 12+78 block recognition remains scientific
    true   -- generated once that block recognition exists
    false  -- actual zeta recognition remains scientific input
    false  -- actual zeta^2 transport/recognition remains live
    false  -- corrected: wrong target for central-trivial phase
    true   -- correct representation type
    false  -- actual quotient-character/orbit decomposition remains live
    false  -- follows a real fixed-phase split
    false  -- downstream of literal residual

fin90CompletedClass : SearchClass
fin90CompletedClass = GENERATED

ninetyRecognitionPaymentClass : SearchClass
ninetyRecognitionPaymentClass = PRUNED

nineOneTwoSixClass : SearchClass
nineOneTwoSixClass = OWNED

productFactorisationClass : SearchClass
productFactorisationClass = LIVE

twelveSeventyEightClass : SearchClass
twelveSeventyEightClass = LIVE

productVsBlockClass : SearchClass
productVsBlockClass = DOWNSTREAM

zetaRecognitionClass : SearchClass
zetaRecognitionClass = LIVE

fixed729RecognitionClass : SearchClass
fixed729RecognitionClass = CORRECTED

fixedAbelianQuotientClass : SearchClass
fixedAbelianQuotientClass = LIVE

literalResidual53Class : SearchClass
literalResidual53Class = DOWNSTREAM

------------------------------------------------------------------------
-- Decisive Round-16 picture:
--
--   196883
--      = 53 + 196830
--      = 53 + 3 * 65610
--      = 53 + 3 * [729 * 90]
--      = 53 + 3 * [3^6 * (10 * 3^2)].
--
-- Character-level outer 3: OWNED regular C3.
-- Nontrivial phases: 729 x 90 Stone-von-Neumann target.
-- Multiplicity 90: Generated carrier/action chart Completed10 x T^2.
-- Fixed phase: NOT another 729 x 90 Stone-von-Neumann module; use the
-- central-trivial quotient E/Z(E)=F3^12 and compute its actual inertia-orbit /
-- linear-character decomposition.  The 53 is the excess fixed-phase piece.
------------------------------------------------------------------------
