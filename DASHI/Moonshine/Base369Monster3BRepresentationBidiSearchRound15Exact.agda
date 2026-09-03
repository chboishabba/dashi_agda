module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound15Exact where

------------------------------------------------------------------------
-- ROUND 15: FIN90 ~= COMPLETED10 x T^2 IS COMPILER OUTPUT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

record Round15Status : Set where
  constructor round15Status
  field
    mixedRadixFin90ToFin10TimesFin9 : Bool
    fin10ToCompletedTenOwned : Bool
    fin9ToLiteralTritSquareOwned : Bool
    fin90ToCompletedTenTimesTritSquareTwoSided : Bool
    actualMultiplicityActionTransportedToCompletedCarrier : Bool
    oldTenByNineRecognitionAttachmentGenerated : Bool
    oldCompletedRecognitionAttachmentGenerated : Bool
    separateNinetyCarrierRecognitionStillNeeded : Bool
    productActionFactorisationProved : Bool
    coarseProjectionDescentProved : Bool
    tritSquareProjectionDescentProved : Bool
    couplingWitnessInfrastructureOwned : Bool
    twelvePlusSeventyEightSameCarrierStillAvailable : Bool
    actualZetaRecognition : Bool
    fixedRegularBlockRecognition : Bool
    literalResidualFiftyThree : Bool

canonicalRound15Status : Round15Status
canonicalRound15Status =
  round15Status
    true   -- Data.Fin remQuot/combine
    true   -- existing completed coarse 10 chart
    true   -- existing literal T^2 chart
    true   -- compiled composition
    true   -- transport by conjugation through the chart
    true   -- old ActualMultiplicityTenByNineAttachment compiler
    true   -- old completed attachment compiler
    false  -- pruned as an independent scientific leaf
    false  -- live: actual dynamics may couple the two coordinates
    false  -- live projection-descent test
    false  -- live projection-descent test
    true   -- exact positive/negative interfaces now owned
    true   -- existing 12+78 chart remains on the same literal Fin90
    false  -- existing scientific input remains live
    false  -- fixed-sector regular block remains live
    false  -- follows fixed-sector split

data SearchClass : Set where
  OWNED GENERATED LIVE DOWNSTREAM PRUNED PARALLEL : SearchClass

mixedRadixCarrierClass : SearchClass
mixedRadixCarrierClass = OWNED

completedNinetyCarrierClass : SearchClass
completedNinetyCarrierClass = GENERATED

transportedActualActionClass : SearchClass
transportedActualActionClass = GENERATED

oldNinetyRecognitionClass : SearchClass
oldNinetyRecognitionClass = PRUNED

productFactorisationClass : SearchClass
productFactorisationClass = LIVE

coarseDescentClass : SearchClass
coarseDescentClass = LIVE

tritSquareDescentClass : SearchClass
tritSquareDescentClass = LIVE

couplingWitnessClass : SearchClass
couplingWitnessClass = OWNED

twelveSeventyEightClass : SearchClass
twelveSeventyEightClass = PARALLEL

zetaRecognitionClass : SearchClass
zetaRecognitionClass = LIVE

fixedRegularClass : SearchClass
fixedRegularClass = LIVE

literalResidual53Class : SearchClass
literalResidual53Class = DOWNSTREAM

------------------------------------------------------------------------
-- Decisive Round-15 picture:
--
--   Fin90
--      |
--      | mixed-radix compiler
--      v
--   Fin10 x Fin9
--      |
--      | semantic charts
--      v
--   Completed10 x T^2
--
-- and the actual multiplicity inertia action is transported through the same
-- two-sided chart.  Therefore carrier/action recognition itself is no longer
-- a scientific payment.
--
-- The live theorem is strictly stronger:
--
--   A(c,t) = (A10(c), AT2(t)) ?
--
-- If either output projection depends on the other input coordinate, the new
-- coupling witnesses block the corresponding descent exactly.  Thus 90=10*3^2
-- can remain a valid carrier decomposition even if the actual dynamics are
-- irreducibly coupled across the two factors.
------------------------------------------------------------------------
