module DASHI.Physics.YangMills.BalabanClayT4SUNWilsonActionConventionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _/_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieLatticeGauge
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.SUNMatrixCarrier
import DASHI.Physics.YangMills.SUNWilsonAction as Wilson
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta

------------------------------------------------------------------------
-- Literal action convention used by the one-loop coefficient ledger.
--
-- K. G. Wilson,
-- "Confinement of quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445
--
-- R. Dashen and D. J. Gross,
-- "Relationship between lattice and continuum definitions of the gauge-theory
-- coupling",
-- Physical Review D 23 (1981), 2340--2348.
-- DOI: 10.1103/PhysRevD.23.2340
--
-- `Wilson.sunWilsonAction` is already the literal plaquette sum
--
--   sum_p [1 - (1/N) Re Tr U_p].
--
-- This module fixes the remaining convention by defining the physical bare
-- action to be exactly
--
--   S_W(U) = (1/g^2) * Wilson.sunWilsonAction(U).
--
-- The one-loop running coefficient is then attached to this same inverse-g^2
-- owner.  No certificate may mix this action with a beta coefficient written
-- for g or g^2 without an explicit conversion theorem.
------------------------------------------------------------------------

record ScaledSUNWilsonActionData
    {N : Nat} {Matrix Complex Scalar Vertex : Set}
    (theory : CertifiedSUNMatrixTheory N Matrix Complex)
    (Edge : Vertex → Vertex → Set) : Set₁ where
  field
    wilsonData : Wilson.SUNWilsonActionData {Scalar = Scalar} theory Edge

    inverseCouplingSq : Scalar
    multiply : Scalar → Scalar → Scalar

    scaledWilsonAction :
      GaugeField {G = SUNMatrixElement theory} Edge → Scalar

    scaledWilsonActionDefinition : ∀ field →
      scaledWilsonAction field
      ≡ multiply inverseCouplingSq (Wilson.sunWilsonAction wilsonData field)

open ScaledSUNWilsonActionData public

scaledSUNWilsonActionGaugeInvariant :
  ∀ {N : Nat} {Matrix Complex Scalar Vertex : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex}
    {Edge : Vertex → Vertex → Set}
    (dataSet : ScaledSUNWilsonActionData theory Edge)
    (gamma : GaugeTransformation Vertex (SUNMatrixElement theory))
    (field : GaugeField {G = SUNMatrixElement theory} Edge) →
  scaledWilsonAction dataSet
    (gaugeAction (sunMatrixGroup theory) gamma field)
  ≡ scaledWilsonAction dataSet field
scaledSUNWilsonActionGaugeInvariant {theory = theory} dataSet gamma field =
  trans
    (scaledWilsonActionDefinition dataSet
      (gaugeAction (sunMatrixGroup theory) gamma field))
    (trans
      (cong
        (multiply dataSet (inverseCouplingSq dataSet))
        (Wilson.sunWilsonActionGaugeInvariant
          (wilsonData dataSet) gamma field))
      (sym (scaledWilsonActionDefinition dataSet field)))

record WilsonActionOneLoopFlow
    {N : Nat} {Matrix Complex Scalar Vertex : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex}
    {Edge : Vertex → Vertex → Set}
    (actionData : ScaledSUNWilsonActionData theory Edge) : Set₁ where
  field
    casimirAdjoint : ℚ
    embedRational : ℚ → Scalar
    inversePiSquared logBlocking : Scalar
    add : Scalar → Scalar → Scalar

    nextInverseCouplingSq : Scalar

    oneLoopInverseCouplingRecursion :
      nextInverseCouplingSq
      ≡ add (inverseCouplingSq actionData)
          (multiply actionData
            (multiply actionData
              (embedRational
                (Beta.pureYMInverseCouplingCoefficient casimirAdjoint))
              inversePiSquared)
            logBlocking)

open WilsonActionOneLoopFlow public

oneLoopWilsonActionUsesElevenOverTwentyFour :
  ∀ {N : Nat} {Matrix Complex Scalar Vertex : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex}
    {Edge : Vertex → Vertex → Set}
    {actionData : ScaledSUNWilsonActionData theory Edge}
    (flow : WilsonActionOneLoopFlow actionData) →
  nextInverseCouplingSq flow
  ≡ add flow (inverseCouplingSq actionData)
      (multiply actionData
        (multiply actionData
          (embedRational flow ((+ 11 / 24) * casimirAdjoint flow))
          (inversePiSquared flow))
        (logBlocking flow))
oneLoopWilsonActionUsesElevenOverTwentyFour {actionData = actionData} flow =
  trans
    (oneLoopInverseCouplingRecursion flow)
    (cong
      (λ rationalCoefficient →
        add flow (inverseCouplingSq actionData)
          (multiply actionData
            (multiply actionData
              (embedRational flow rationalCoefficient)
              (inversePiSquared flow))
            (logBlocking flow)))
      (Beta.inverseCouplingIsElevenOverTwentyFour
        (casimirAdjoint flow)))

oneLoopWilsonActionUsesBetaZeroOverEight :
  ∀ {N : Nat} {Matrix Complex Scalar Vertex : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex}
    {Edge : Vertex → Vertex → Set}
    {actionData : ScaledSUNWilsonActionData theory Edge}
    (flow : WilsonActionOneLoopFlow actionData) →
  nextInverseCouplingSq flow
  ≡ add flow (inverseCouplingSq actionData)
      (multiply actionData
        (multiply actionData
          (embedRational flow
            ((+ 1 / 8) * Beta.pureYMBetaZero (casimirAdjoint flow)))
          (inversePiSquared flow))
        (logBlocking flow))
oneLoopWilsonActionUsesBetaZeroOverEight {actionData = actionData} flow =
  trans
    (oneLoopInverseCouplingRecursion flow)
    (cong
      (λ rationalCoefficient →
        add flow (inverseCouplingSq actionData)
          (multiply actionData
            (multiply actionData
              (embedRational flow rationalCoefficient)
              (inversePiSquared flow))
            (logBlocking flow)))
      (Beta.inverseCouplingIsBetaZeroOverEight
        (casimirAdjoint flow)))

scaledSUNWilsonActionConventionLevel : ProofLevel
scaledSUNWilsonActionConventionLevel = machineChecked

scaledSUNWilsonGaugeInvarianceLevel : ProofLevel
scaledSUNWilsonGaugeInvarianceLevel = machineChecked

wilsonActionBetaConventionBridgeLevel : ProofLevel
wilsonActionBetaConventionBridgeLevel = machineChecked

-- The remaining physical calculation is to extract the plaquette coefficient
-- of the exact RG effective action and inhabit oneLoopInverseCouplingRecursion.
-- The convention itself and both equivalent coefficient notations are closed.
physicalWilsonPlaquetteExtractionLevel : ProofLevel
physicalWilsonPlaquetteExtractionLevel = conditional
