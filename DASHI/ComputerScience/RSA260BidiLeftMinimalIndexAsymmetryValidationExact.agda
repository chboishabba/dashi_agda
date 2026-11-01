module DASHI.ComputerScience.RSA260BidiLeftMinimalIndexAsymmetryValidationExact where

------------------------------------------------------------------------
-- RED/GREEN REGRESSION ROOT
--
-- This validation surface intentionally imports the production owner before
-- that owner exists.  The source-level RED condition is therefore the missing
-- module itself; kernel certification remains a separate status coordinate.
------------------------------------------------------------------------

import DASHI.ComputerScience.RSA260BidiLeftMinimalIndexAsymmetryExact as LeftIndex

leftMinimalIndexBoundary : LeftIndex.LeftMinimalIndexInterpretationBoundary
leftMinimalIndexBoundary = LeftIndex.canonicalLeftMinimalIndexInterpretationBoundary

squareOnlyDefect :
  LeftIndex.SquareExtensionAdequacyDefect
squareOnlyDefect = LeftIndex.squareExtensionCannotDetermineOrientation

refinedObserverAdequate :
  LeftIndex.RefinedOrientationAdequacy
refinedObserverAdequate = LeftIndex.orientationFactorsThroughRefinedObserver

firstResidual : LeftIndex.LeftMinimalIndexResidual
firstResidual = LeftIndex.firstLeftMinimalIndexResidual
