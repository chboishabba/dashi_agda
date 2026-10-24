module DASHI.Physics.QFT.MMPWilsonHadamardSameBackgroundBidiExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Physics.YangMills.CompactLieGroupCore as Group
import DASHI.Physics.YangMills.CompactLieGroupDerived as Derived
import DASHI.Physics.YangMills.CompactLieLatticeGauge as Wilson
import DASHI.Physics.QFT.MMPDiracCauchyNoncompactCompactDoubleBidiExact as Cauchy
import DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface as AQFT
import DASHI.Physics.QuantumVacuum.CasimirResidualCauchyToLimitExact as Casimir

------------------------------------------------------------------------
-- Source provenance / DO NOT DOUBLE COUNT:
-- Wilson open-path endpoint covariance and closed-loop class-function
-- invariance are EXISTING internal DASHI Wilson/Gauge math owners.
-- Hadamard wavefront-set condition is EXTERNAL Dirac AQFT mathematics:
-- Sahlmann--Verch; Gerard--Stoskopf 2022; Capoferri--Murro 2025.
-- Jochen Zahn 2014 owns locally covariant charged Dirac Wick subtraction.
-- This adapter DOES NOT construct a Hadamard 2-pt distribution.
------------------------------------------------------------------------

-- Direct reuse of the actual exact internal endpoint-indexed Wilson theorem.
-- Re-exporting a theorem does not claim a newly discovered mathematical law.
nativeWilsonOpenPathGaugeCovariant :
  ∀ {Vertex G : Set}
    {Edge : Vertex → Vertex → Set}
    {x y : Vertex}
  (H : Group.Group G)
  (gamma : Wilson.GaugeTransformation Vertex G)
  (U : Wilson.GaugeField Edge)
  (path : Wilson.Path Edge x y) →
  Wilson.holonomy H (Wilson.gaugeAction H gamma U) path
  ≡
  Group.multiply H
    (Group.multiply H (gamma x) (Wilson.holonomy H U path))
    (Group.inverse H (gamma y))
nativeWilsonOpenPathGaugeCovariant =
  Wilson.holonomyGaugeCovariant

-- Distinguishes linear Hadamard matrices from the microlocal Hadamard state.
data HadamardMeaning : Set where
  finiteOrthogonalMatrix : HadamardMeaning
  fermionicTwoPointMicrolocalSpectrum : HadamardMeaning

matrixHadamardIsNotMicrolocalQuantumState :
  finiteOrthogonalMatrix ≡ fermionicTwoPointMicrolocalSpectrum → ⊥
matrixHadamardIsNotMicrolocalQuantumState ()

------------------------------------------------------------------------
-- Algebraic COMMON subtraction cancellation, analogous to taking the
-- relative difference between states sharing the same local parametrix.
-- This is ONLY group algebra; smoothness, CAR, positivity and wavefront
-- properties are not supplied by an arbitrary group.
--
-- The cancellation IS NOT new: it reuses the existing generic exact
-- group gauge telescope owner without duplicating a proof.
------------------------------------------------------------------------

commonParametrixTelescope :
  ∀ {Kernel : Set}
    (H : Group.Group Kernel)
    (stateOne commonReference stateTwo : Kernel) →
  Group.multiply H
    (Group.multiply H
      (Group.multiply H stateOne (Group.identity H))
      (Group.inverse H commonReference))
    (Group.multiply H
      (Group.multiply H commonReference (Group.identity H))
      (Group.inverse H stateTwo))
  ≡
  Group.multiply H
    (Group.multiply H stateOne
      (Group.multiply H (Group.identity H) (Group.identity H)))
    (Group.inverse H stateTwo)
commonParametrixTelescope H stateOne commonReference stateTwo =
  Derived.gaugeTelescope H
    stateOne commonReference stateTwo
    (Group.identity H) (Group.identity H)

nativeNoncompactCauchyBoundary : Set
nativeNoncompactCauchyBoundary =
  Cauchy.NoncompactCauchyDiracSourceBoundary

nativeAQFTTimeSliceStillTargetOnly : Set
nativeAQFTTimeSliceStillTargetOnly =
  AQFT.TimeSliceTheoremStatus

-- Existing native Bishop/constructed-real residual: once a true same-
-- background, same-parametrix REGULATOR DIFFERENCE is supplied and proved
-- Cauchy, this owner ALREADY constructs its renormalized limit. Completeness
-- does not itself manufacture the residual tail estimate.
nativeCasimirResidualSequenceOwner : Set₁
nativeCasimirResidualSequenceOwner =
  Casimir.ResidualRegulatorSequence


-- Conditional theorem: a specified common point-split reference and
-- a smooth physical two-point difference give a well-defined finite
-- *difference* observable. No source data have been constructed here.
record SameBackgroundChargedHadamardDifference
    (ChargedTwoPoint FiniteObservable : Set) : Set₁ where
  field
    sharedMetricAndSpinCConnection : Set
    sharedSource : sharedMetricAndSpinCConnection

    stateOne : ChargedTwoPoint
    stateTwo : ChargedTwoPoint
    twoPointDifference : ChargedTwoPoint
    differenceHasCorrectPhysicalCAR : Set
    carWitness : differenceHasCorrectPhysicalCAR
    differenceSmoothAcrossCoincidence : Set
    smoothWitness : differenceSmoothAcrossCoincidence

    gaugeTransportDressedPointSplit :
      ChargedTwoPoint → FiniteObservable
    stateDifferenceFinite : FiniteObservable

    -- To identify stateDifferenceFinite with a DIFFERENCE OF physical
    -- renormalized stress/current, one must still construct a literal
    -- 4D Dirac point-splitting bidifferential operator and spin/gauge
    -- parallel transport. This is an equality INPUT, not a theorem.
    pointSplitDifferenceMatchesObservable :
      gaugeTransportDressedPointSplit twoPointDifference
        ≡ stateDifferenceFinite

open SameBackgroundChargedHadamardDifference public

conditionalHadamardStateDifferenceObservable :
  ∀ {ChargedTwoPoint FiniteObservable}
    (dataSet :
      SameBackgroundChargedHadamardDifference
        ChargedTwoPoint FiniteObservable) →
  gaugeTransportDressedPointSplit dataSet
    (twoPointDifference dataSet)
    ≡ stateDifferenceFinite dataSet
conditionalHadamardStateDifferenceObservable dataSet =
  pointSplitDifferenceMatchesObservable dataSet

record PhysicalPromotionBoundary : Set where
  field
    exactWilsonTransportTheoremImported : Bool
    sameReferenceCancellationAlgebraProved : Bool
    chargedSpinCCARHadamardWavefrontConstructed : Bool
    noncompactHandlePhysicalSpinorCovarianceConstructed : Bool
    actualFourDimensionalDiracStressCurrentComputed : Bool
    coupledMaxwellEinsteinEquationsSolved : Bool

canonicalPromotionBoundary : PhysicalPromotionBoundary
canonicalPromotionBoundary = record
  { exactWilsonTransportTheoremImported = true
  ; sameReferenceCancellationAlgebraProved = true
  ; chargedSpinCCARHadamardWavefrontConstructed = false
  ; noncompactHandlePhysicalSpinorCovarianceConstructed = false
  ; actualFourDimensionalDiracStressCurrentComputed = false
  ; coupledMaxwellEinsteinEquationsSolved = false
  }

theoremStateSourceStillMissing :
  PhysicalPromotionBoundary.chargedSpinCCARHadamardWavefrontConstructed
    canonicalPromotionBoundary ≡ false
theoremStateSourceStillMissing = refl
