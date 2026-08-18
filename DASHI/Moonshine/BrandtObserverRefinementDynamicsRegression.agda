module DASHI.Moonshine.BrandtObserverRefinementDynamicsRegression where

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.PredicatePullbackLatticeExact as Predicate
import DASHI.Core.ProvenanceBearingQuotient as Provenance
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned

import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11P37HeckeFrobeniusJointSpectrumExact as Joint
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as Decomp
import DASHI.Moonshine.BrandtObserverRefinementDynamicsBridgeExact as Bridge
import DASHI.Moonshine.P11Fine5PNFProvenanceQuotientBridgeExact as Reopen
import DASHI.Moonshine.P11Fine5PredicateDescentBridgeExact as Descent

minusTwoRefinementRegression :
  Observer.StrictRefinement
    Bridge.t2MinusTwoObserver
    (Observer.pairObserver Bridge.t2MinusTwoObserver Bridge.frobeniusParityObserver)
minusTwoRefinementRegression = Bridge.minusTwoT2ToFrobeniusStrictRefinement

jointFingerprintStillCollidesRegression :
  Observer.Separating Bridge.jointT3T5FObserver → ⊥
jointFingerprintStillCollidesRegression = Bridge.jointT3T5FNotSeparating

deckTypeStrictRefinementRegression :
  Observer.StrictRefinement
    Bridge.jointT3T5FObserver
    (Observer.pairObserver Bridge.jointT3T5FObserver Bridge.deckRepresentationTypeObserver)
deckTypeStrictRefinementRegression = Bridge.jointFingerprintToDeckTypeStrictRefinement

markedFrobeniusVerticalRegression :
  Dynamics.HiddenTransition
    Bridge.p11MarkedJCore
    DASHI.Moonshine.P11MarkedX2FrobeniusFrickeExact.markedFrobenius
    Fine.a0
markedFrobeniusVerticalRegression = Bridge.markedFrobeniusHiddenTransition

markedReopeningRegression :
  Reopen.reopenFine5 Geo.j1728SS Reopen.r2 ≡ Fine.b2
markedReopeningRegression = Reopen.b2ReopensFromCoarseAndResidual

markedPredicateDoesNotDescendRegression :
  Predicate.FibreConstantPredicate Fine.projectFine5 Descent.isMarkedA0 → ⊥
markedPredicateDoesNotDescendRegression = Descent.markedA0PredicateNotFibreConstant
