module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverJoinValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverJoinExact as J

------------------------------------------------------------------------
-- RED/GREEN validation root for the AdK two-axis observer join.
------------------------------------------------------------------------

joinRegression :
  J.AdKFRETObserverJoinBoundary.singleLidNmpAxisRetainsBothDeclaredAxes
    J.canonicalAdKFRETObserverJoinBoundary
  ≡ false
  × J.AdKFRETObserverJoinBoundary.singleLidCoreAxisRetainsBothDeclaredAxes
    J.canonicalAdKFRETObserverJoinBoundary
  ≡ false
  × J.AdKFRETObserverJoinBoundary.joinedObserverRetainsBothDeclaredAxes
    J.canonicalAdKFRETObserverJoinBoundary
  ≡ true
joinRegression = refl , refl , refl

strictnessRegression :
  J.AdKFRETObserverJoinBoundary.joinStrictlyRicherThanEitherAxisInFiniteWitness
    J.canonicalAdKFRETObserverJoinBoundary
  ≡ true
  × J.AdKFRETObserverJoinBoundary.joinedDeclaredAxisAdequacyMeansCompleteProteinState
    J.canonicalAdKFRETObserverJoinBoundary
  ≡ false
strictnessRegression = refl , refl

historicalBoundaryRegression :
  J.AdKFRETObserverJoinBoundary.historicalExperimentsWereSimultaneousSameMoleculeReadouts
    J.canonicalAdKFRETObserverJoinBoundary
  ≡ false
  × J.AdKFRETObserverJoinBoundary.joinConstructionCreatesNewExperimentalData
    J.canonicalAdKFRETObserverJoinBoundary
  ≡ false
historicalBoundaryRegression = refl , refl
