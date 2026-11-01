module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverAxisValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverAxisExact as F

------------------------------------------------------------------------
-- RED/GREEN validation root: one-dimensional FRET observations are indexed by
-- the chosen residue/domain axis.  Same protein/context does not make different
-- label geometries informationally interchangeable.
------------------------------------------------------------------------

axisRegression :
  F.AdKFRETObserverBoundary.lidNmpAxisSourcePaid F.canonicalAdKFRETObserverBoundary ≡ true
  × F.AdKFRETObserverBoundary.lidCoreAxisSourcePaid F.canonicalAdKFRETObserverBoundary ≡ true
axisRegression = refl , refl

populationInterpretationRegression :
  F.AdKFRETObserverBoundary.lidNmpExperimentOpenMajor F.canonicalAdKFRETObserverBoundary ≡ true
  × F.AdKFRETObserverBoundary.lidCoreExperimentClosedFavoured F.canonicalAdKFRETObserverBoundary ≡ true
populationInterpretationRegression = refl , refl

nonPromotionRegression :
  F.AdKFRETObserverBoundary.oneFRETAxisDeterminesFullConformation F.canonicalAdKFRETObserverBoundary ≡ false
  × F.AdKFRETObserverBoundary.differentLabelAxesAreInterchangeable F.canonicalAdKFRETObserverBoundary ≡ false
  × F.AdKFRETObserverBoundary.populationDifferenceProvesExperimentalContradiction F.canonicalAdKFRETObserverBoundary ≡ false
nonPromotionRegression = refl , refl , refl

observerRefinementRegression :
  F.AdKFRETObserverBoundary.axisIdentityRequiredForInterpretation F.canonicalAdKFRETObserverBoundary ≡ true
  × F.AdKFRETObserverBoundary.multiAxisObservationStrictlyRicherThanAxisErasedObservation F.canonicalAdKFRETObserverBoundary ≡ true
observerRefinementRegression = refl , refl
