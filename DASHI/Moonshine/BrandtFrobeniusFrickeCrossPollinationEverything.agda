module DASHI.Moonshine.BrandtFrobeniusFrickeCrossPollinationEverything where

------------------------------------------------------------------------
-- Focused aggregate for the finite Brandt / level-2 / Frobenius / Fricke /
-- character convergence lane.
--
-- It intentionally imports both positive results and falsifiers:
-- quotient-observable factorization does not imply carrier identity; the naive
-- ell=2 edge-slot C3 action fails; coarse Fricke fixed points are not the same
-- carrier as Brandt j-classes; all-fixed Frobenius is carrier-sensitive under
-- level rigidification; and observer refinement is tracked explicitly.
------------------------------------------------------------------------

import DASHI.Core.ObserverRefinementLatticeExact
import DASHI.Core.FibrePreservingDynamicsExact

import DASHI.Foundations.FibreConstantObservableExact
import DASHI.Foundations.Phase3RootCharacterWeldExact
import DASHI.Foundations.TernaryNineRingFieldFibreSeparationExact
import DASHI.Foundations.CyclicNineCharacterPullbackExact
import DASHI.Foundations.F9FrobeniusInvolutionNormalFormExact

import DASHI.Moonshine.PrimeRegularHeckeLocalGeometryExact
import DASHI.Moonshine.P11T2TernarySlotCharacterNoGoExact
import DASHI.Moonshine.P11BrandtFrobeniusFrickeCarrierSeparationExact
import DASHI.Moonshine.BrandtFrickeCarrierCountControlsExact
import DASHI.Moonshine.P11GeometricFrobeniusRealizationExact
import DASHI.Moonshine.P11Fine5FibreObservableBridgeExact
import DASHI.Moonshine.P11MarkedFrobeniusQuotientDefectExact
import DASHI.Moonshine.P11MarkedX2C3CharacterWeldExact
import DASHI.Moonshine.P11MarkedX2FrobeniusFrickeExact
import DASHI.Moonshine.P11MarkedX2HeckeAlgebraExact
import DASHI.Moonshine.P11MarkedX2PrimeSquareNeighboursExact
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact
import DASHI.Moonshine.BrandtObserverRefinementDynamicsBridgeExact

import DASHI.Moonshine.P13OggOneClassHeckeControlExact
import DASHI.Moonshine.P37SageSupersingularFrobeniusExact
import DASHI.Moonshine.P11P37HeckeFrobeniusJointSpectrumExact
import DASHI.Moonshine.P37SourceForcedT3T5HeckeExact
import DASHI.Moonshine.P37JointHeckeAlgebraExact
import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact
import DASHI.Moonshine.P37MarkedX2FrobeniusFrickeExact
import DASHI.Moonshine.P37MarkedLegendreT3T5Exact
import DASHI.Moonshine.P37MarkedX2HeckeFrobeniusFrickeExact
import DASHI.Moonshine.P37MarkedX2DeckTorsorExact
import DASHI.Moonshine.P37MarkedX2DeckOrbitalHeckeExact
import DASHI.Moonshine.P37MarkedX2DeckOrbitalPermutationExact

import DASHI.Moonshine.BrandtHeckeFrobeniusFrickeSelectorWeldExact
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact
import DASHI.Moonshine.PrimeFrickeOrbitSaturationExact

import DASHI.Moonshine.AristotleZetaFrobeniusCrossPollinationEverything
