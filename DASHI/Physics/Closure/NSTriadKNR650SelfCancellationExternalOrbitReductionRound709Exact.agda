{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SelfCancellationExternalOrbitReductionRound709Exact where

------------------------------------------------------------------------
-- ROUND709 / IF THE R708 SELF ORBIT CANCELS, THE FULL R700 ORBIT IS EXACTLY
--            THE EXTERNAL ORBIT
--
-- R708 proves on the literal complete carrier
--
--   FullOrbit = SelfOrbit + ExternalOrbit.
--
-- Do not create two new analytic leaves.  The highest-alpha exact-cancellation
-- test is the SELF orbit.  If that finite orbit vanishes, then the complete
-- Clay-facing nested orbit is definitionally reduced to the external residue:
--
--   SelfOrbit = 0  ->  FullOrbit = ExternalOrbit.
--
-- This compiler is deliberately one-way and least-privilege.  It does not
-- assume self cancellation, does not estimate the external term, and does not
-- split the eventual spacetime theorem into independent budgets.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650UnitNestedOrbitSelfExternalSplitRound708Exact as R708

module Reduction
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R694.F)
    (S : Helical.HelicalModeScalars R694.F)
    (L : Helical.PeriodicHelicalProjectorLaws R694.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Split =
    R708.UnitOrbitSplit physicalSystem S L H velocityTransverse

  items =
    Physical.physicalTriadEnumeration Split.Full.Nested.Base.cutoff

  fullOrbit : ℚ
  fullOrbit =
    R38.foldPower Split.Full.nestedTriadOrbitResidue items

  selfOrbit : ℚ
  selfOrbit =
    Split.foldSelfOrbit items

  externalOrbit : ℚ
  externalOrbit =
    Split.foldExternalOrbit items

  fullOrbitSplits : fullOrbit ≡ selfOrbit + externalOrbit
  fullOrbitSplits =
    Split.completeNestedOrbitSplitsSelfExternal

  selfCancellationReducesFullToExternal :
    selfOrbit ≡ 0ℚ →
    fullOrbit ≡ externalOrbit
  selfCancellationReducesFullToExternal selfZero =
    trans
      fullOrbitSplits
      (trans
        (cong (_+ externalOrbit) selfZero)
        refl)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round709SelfCancellationWouldReduceFullOrbitToExternalExactly : Bool
round709SelfCancellationWouldReduceFullOrbitToExternalExactly = true

round709CreatesSeparateSelfAndExternalAnalyticBudgets : Bool
round709CreatesSeparateSelfAndExternalAnalyticBudgets = false

round709SelfOrbitExactCancellationClosed : Bool
round709SelfOrbitExactCancellationClosed = false

round709ExternalOrbitCutoffUniformSpacetimePaymentClosed : Bool
round709ExternalOrbitCutoffUniformSpacetimePaymentClosed = false

round709IntroducesEstimate : Bool
round709IntroducesEstimate = false

round709ClayPromotion : Bool
round709ClayPromotion = false

round709SelfCancellationWouldReduceFullOrbitToExternalExactlyIsTrue :
  round709SelfCancellationWouldReduceFullOrbitToExternalExactly ≡ true
round709SelfCancellationWouldReduceFullOrbitToExternalExactlyIsTrue = refl

round709CreatesSeparateSelfAndExternalAnalyticBudgetsIsFalse :
  round709CreatesSeparateSelfAndExternalAnalyticBudgets ≡ false
round709CreatesSeparateSelfAndExternalAnalyticBudgetsIsFalse = refl

round709SelfOrbitExactCancellationClosedIsFalse :
  round709SelfOrbitExactCancellationClosed ≡ false
round709SelfOrbitExactCancellationClosedIsFalse = refl

round709ExternalOrbitCutoffUniformSpacetimePaymentClosedIsFalse :
  round709ExternalOrbitCutoffUniformSpacetimePaymentClosed ≡ false
round709ExternalOrbitCutoffUniformSpacetimePaymentClosedIsFalse = refl

round709IntroducesEstimateIsFalse :
  round709IntroducesEstimate ≡ false
round709IntroducesEstimateIsFalse = refl

round709ClayPromotionIsFalse :
  round709ClayPromotion ≡ false
round709ClayPromotionIsFalse = refl
