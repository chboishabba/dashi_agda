module DASHI.Physics.QuantumVacuum.CasimirSide4CartanCurvatureClosureValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.QuantumVacuum.CasimirSide4CartanCurvatureClosureExact as C

side4CartanClosureOwnedRegression :
  C.side4CartanFieldToCartanCurlCompilerOwned
    C.canonicalSide4CartanCurvatureBoundary ≡ true
side4CartanClosureOwnedRegression = refl

transverseCurlVanishesRegression :
  C.transverseLieCoordinateCurlVanishes
    C.canonicalSide4CartanCurvatureBoundary ≡ true
transverseCurlVanishesRegression = refl

selectedNonlinearBridgeStillOpenRegression :
  C.selectedNonlinearFieldIdentifiedWithSide4FlatField
    C.canonicalSide4CartanCurvatureBoundary ≡ false
selectedNonlinearBridgeStillOpenRegression = refl

flatClosureDoesNotPromoteNonlinearRegression :
  C.FlatSide4CartanClosureAutomaticallyIdentifiesSelectedNonlinearCurvature → ⊥
flatClosureDoesNotPromoteNonlinearRegression =
  C.flatSide4ClosureDoesNotIdentifySelectedNonlinearCurvature
