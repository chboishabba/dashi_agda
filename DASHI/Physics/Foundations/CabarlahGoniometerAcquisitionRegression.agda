module DASHI.Physics.Foundations.CabarlahGoniometerAcquisitionRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.CabarlahGoniometerAcquisitionExact as Cabarlah

------------------------------------------------------------------------
-- RED contract: this regression is introduced before the production owner.
------------------------------------------------------------------------

cabarlahDFLineageRequired : Cabarlah.CabarlahDirectionFindingAcquisition
cabarlahDFLineageRequired = Cabarlah.canonicalCabarlahDirectionFindingAcquisition

cabarlahGoniometerBoundaryRequired : Cabarlah.CabarlahGoniometerBoundary
cabarlahGoniometerBoundaryRequired = Cabarlah.canonicalCabarlahGoniometerBoundary

cabarlahCrossPollinationRequired : Cabarlah.CabarlahObserverCrossPollination
cabarlahCrossPollinationRequired = Cabarlah.canonicalCabarlahObserverCrossPollination
