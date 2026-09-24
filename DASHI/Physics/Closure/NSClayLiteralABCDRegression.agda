module DASHI.Physics.Closure.NSClayLiteralABCDRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayLiteralABCDExact as ABCD
import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as B
import DASHI.Physics.Closure.NSTriadKNClayForcedBreakdownFormulationRound523Exact as CD

------------------------------------------------------------------------
-- Literal theorem-surface regression.
--
-- This checks the exact shape of the capstone without pretending that theorem
-- statement construction is theorem inhabitation.
------------------------------------------------------------------------

statementAConstructed :
  ABCD.literalFeffermanStatementAConstructed ≡ true
statementAConstructed = refl

statementBIsCanonicalExistingLiteralOwner :
  ABCD.literalFeffermanStatementBReused ≡ true
statementBIsCanonicalExistingLiteralOwner =
  B.literalFeffermanPeriodicStatementConstructedIsTrue

statementCConstructed :
  ABCD.literalFeffermanStatementCConstructed ≡ true
statementCConstructed = refl

statementDConstructed :
  ABCD.literalFeffermanStatementDConstructed ≡ true
statementDConstructed = refl

capstoneConstructed :
  ABCD.literalABCDCapstoneConstructed ≡ true
capstoneConstructed = refl

capstoneDoesNotManufactureProofs :
  ABCD.literalABCDProofsInhabitedHere ≡ false
capstoneDoesNotManufactureProofs = refl

cRetainsRapidInitialDecay :
  CD.requiredByC523 CD.rapidInitialSpatialDecay523 ≡ true
cRetainsRapidInitialDecay =
  ABCD.cRequiresRapidInitialSpatialDecay

cRetainsRapidForcingDecay :
  CD.requiredByC523 CD.rapidForcingSpaceTimeDecay523 ≡ true
cRetainsRapidForcingDecay =
  ABCD.cRequiresRapidForcingSpaceTimeDecay

cRetainsBoundedEnergyConsumer :
  CD.requiredByC523 CD.boundedEnergyRequirement523 ≡ true
cRetainsBoundedEnergyConsumer =
  ABCD.cRequiresBoundedEnergy

dRetainsPeriodicDatum :
  CD.requiredByD523 CD.periodicInitialDatum523 ≡ true
dRetainsPeriodicDatum =
  ABCD.dRequiresPeriodicInitialDatum

dRetainsRapidTimeDecay :
  CD.requiredByD523 CD.rapidForcingTimeDecay523 ≡ true
dRetainsRapidTimeDecay =
  ABCD.dRequiresRapidForcingTimeDecay

dRetainsPeriodicSolutionConsumer :
  CD.requiredByD523 CD.periodicSolutionRequirement523 ≡ true
dRetainsPeriodicSolutionConsumer =
  ABCD.dRequiresPeriodicSolution
