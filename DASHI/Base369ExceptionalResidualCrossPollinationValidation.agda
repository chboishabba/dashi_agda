module DASHI.Base369ExceptionalResidualCrossPollinationValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Moonshine.Base369ExceptionalAlbertFiftyThreeResidualBidiExact as Residual
import DASHI.Moonshine.Base369Monster3BSeventyEightExceptionalE6BidiExact as E6
import DASHI.Moonshine.Base369MonsterExceptionalHybridBulkResidualBidiExact as Hybrid

exceptional54CandidateRecorded :
  Exceptional.ExceptionalResidualBoundary.fiftyFourAsAlbertPairRecorded
    Exceptional.canonicalExceptionalResidualBoundary ≡ true
exceptional54CandidateRecorded = refl

exceptional53CandidateRecorded :
  Exceptional.ExceptionalResidualBoundary.fiftyThreeAsOneScalarPlusTwo26CandidateRecorded
    Exceptional.canonicalExceptionalResidualBoundary ≡ true
exceptional53CandidateRecorded = refl

exceptional53NotNamedIrrep :
  Exceptional.ExceptionalResidualBoundary.fiftyThreeDeclaredNamedExceptionalIrrepHere
    Exceptional.canonicalExceptionalResidualBoundary ≡ false
exceptional53NotNamedIrrep = refl

base369ResidualNeedsBidi :
  Residual.Base369ExceptionalResidualBoundary.twoSidedCarrierRecognitionRequired
    Residual.canonicalBase369ExceptionalResidualBoundary ≡ true
base369ResidualNeedsBidi = refl

base369ResidualNeedsSameAction :
  Residual.Base369ExceptionalResidualBoundary.sameActualActionRequired
    Residual.canonicalBase369ExceptionalResidualBoundary ≡ true
base369ResidualNeedsSameAction = refl

seventyEightDoesNotIdentifyE6ByDimension :
  E6.SeventyEightExceptionalBoundary.seventyEightDimensionAloneIdentifiesE6
    E6.canonicalSeventyEightExceptionalBoundary ≡ false
seventyEightDoesNotIdentifyE6ByDimension = refl

hybridNeedsOneAmbientAction :
  Hybrid.HybridBulkResidualBoundary.oneAmbientMonsterActionRequired
    Hybrid.canonicalHybridBulkResidualBoundary ≡ true
hybridNeedsOneAmbientAction = refl

hybridDoesNotClaimSharedAlgebra :
  Hybrid.HybridBulkResidualBoundary.sharedAlgebraBetweenBulkAndResidualClaimedHere
    Hybrid.canonicalHybridBulkResidualBoundary ≡ false
hybridDoesNotClaimSharedAlgebra = refl

hybridArithmeticDoesNotCreateDecomposition :
  Hybrid.HybridBulkResidualBoundary.arithmetic196830Plus53CreatesDecomposition
    Hybrid.canonicalHybridBulkResidualBoundary ≡ false
hybridArithmeticDoesNotCreateDecomposition = refl
