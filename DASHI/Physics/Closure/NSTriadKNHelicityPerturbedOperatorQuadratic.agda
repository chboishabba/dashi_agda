module DASHI.Physics.Closure.NSTriadKNHelicityPerturbedOperatorQuadratic where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Zhen Lei; Fang-Hua Lin; Yi Zhou.
-- Title: "Structure of Helicity and Global Solutions of Incompressible
-- Navier-Stokes Equation".
-- Venue/year: Archive for Rational Mechanics and Analysis 218 (2015).
-- DOI: 10.1007/s00205-015-0884-8.
-- Uses: curl spectral splitting and the viscous helicity identity.
-- Relationship: defines a DASHI-original operator-valued perturbation of the
-- H^s quadratic correction.  It does not import conditional helical dominance
-- as a theorem about arbitrary states.
--
-- Corrected mathematical framing (2026-07): The perturbed multiplier
-- eigenvalues on the helical basis are baseWeight(k) +/- epsilon*|k|, so
-- the quadratic form value changes by epsilon*(|u_k^+|^2 - |u_k^-|^2).
-- For modewise helicity-balanced states (|u_k^+| = |u_k^-| at every
-- mode), this perturbation vanishes identically regardless of sign or
-- magnitude of epsilon.  The global helicity perturbation is therefore
-- structurally blind to the entire family of modewise-balanced states.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical

Velocity :
  ∀ {r} (F : C3.RealField r) → Set r
Velocity F = Z3.FourierMode → C3.Complex3 F

OperatorMultiplier :
  ∀ {r} (F : C3.RealField r) → Set r
OperatorMultiplier F =
  Z3.FourierMode → C3.Complex3 F → C3.Complex3 F

mapOperatorWeightedEnergy :
  ∀ {r} {F : C3.RealField r} →
  OperatorMultiplier F →
  Velocity F →
  List Z3.FourierMode →
  List (C3.Carrier F)
mapOperatorWeightedEnergy multiplier velocity [] = []
mapOperatorWeightedEnergy multiplier velocity (k ∷ modes) =
  C3.real
    (C3.hermitianPairing3
      (velocity k)
      (multiplier k (velocity k)))
  ∷ mapOperatorWeightedEnergy multiplier velocity modes

operatorWeightedEnergy :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F →
  List Z3.FourierMode →
  OperatorMultiplier F →
  Velocity F →
  C3.Carrier F
operatorWeightedEnergy {F = F} half modes multiplier velocity =
  C3.multiply F half
    (Helical.sumScalars F
      (mapOperatorWeightedEnergy multiplier velocity modes))

operatorWeightedEnergyDefinition :
  ∀ {r} {F : C3.RealField r}
    (half : C3.Carrier F)
    (modes : List Z3.FourierMode)
    (multiplier : OperatorMultiplier F)
    (velocity : Velocity F) →
  operatorWeightedEnergy half modes multiplier velocity
  ≡
  C3.multiply F half
    (Helical.sumScalars F
      (mapOperatorWeightedEnergy multiplier velocity modes))
operatorWeightedEnergyDefinition half modes multiplier velocity = refl

helicitySignScalar :
  ∀ {r} {F : C3.RealField r} →
  Helical.HelicitySign → C3.Carrier F → C3.Carrier F
helicitySignScalar {F = F} Helical.plus epsilon = epsilon
helicitySignScalar {F = F} Helical.minus epsilon = C3.negate F epsilon

helicityPerturbedMultiplier :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → C3.Carrier F) →
  Helical.HelicitySign →
  C3.Carrier F →
  OperatorMultiplier F
helicityPerturbedMultiplier {F = F} E I baseWeight sign epsilon k value =
  C3.complex3Add
    (C3.complex3Scale
      (C3.realEmbed F (baseWeight k))
      (C3.lerayProject3 E I k value))
    (C3.complex3Scale
      (C3.realEmbed F (helicitySignScalar sign epsilon))
      (Helical.curlSymbol E k value))

helicityPerturbedMultiplierDefinition :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (baseWeight : Z3.FourierMode → C3.Carrier F)
    (sign : Helical.HelicitySign)
    (epsilon : C3.Carrier F)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  helicityPerturbedMultiplier E I baseWeight sign epsilon k value
  ≡
  C3.complex3Add
    (C3.complex3Scale
      (C3.realEmbed F (baseWeight k))
      (C3.lerayProject3 E I k value))
    (C3.complex3Scale
      (C3.realEmbed F (helicitySignScalar sign epsilon))
      (Helical.curlSymbol E k value))
helicityPerturbedMultiplierDefinition E I baseWeight sign epsilon k value =
  refl

record OperatorMultiplierLaws
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (multiplier : OperatorMultiplier F) : Set (lsuc r) where
  field
    operatorMultiplierHermitian :
      ∀ k u v →
      C3.hermitianPairing3 (multiplier k u) v
      ≡ C3.hermitianPairing3 u (multiplier k v)

    operatorMultiplierRealityCompatible :
      ∀ k value →
      multiplier (Z3.negateMode k) (C3.complex3Conjugate value)
      ≡ C3.complex3Conjugate (multiplier k value)

    operatorMultiplierPreservesTransverse :
      ∀ k value →
      Helical.Transverse E k value →
      Helical.Transverse E k (multiplier k value)

    operatorMultiplierCutoffCompatible :
      (N : Nat) (k : Z3.FourierMode) (value : C3.Complex3 F) →
      C3.Complex3 F

open OperatorMultiplierLaws public

record HelicityPerturbedCandidateLaws
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (baseWeight : Z3.FourierMode → C3.Carrier F)
    (sign : Helical.HelicitySign)
    (epsilon : C3.Carrier F) : Set (lsuc r) where
  field
    multiplierLaws :
      OperatorMultiplierLaws F E
        (helicityPerturbedMultiplier E I baseWeight sign epsilon)

    helicalEigenvaluePlus helicalEigenvalueMinus :
      Z3.FourierMode → C3.Carrier F

    helicityPerturbedMultiplierHelicalDiagonalisation :
      (k : Z3.FourierMode) (value : C3.Complex3 F) →
      helicityPerturbedMultiplier E I baseWeight sign epsilon k value
      ≡
      C3.complex3Add
        (C3.complex3Scale
          (C3.realEmbed F (helicalEigenvaluePlus k))
          (Helical.helicalProjectorPlus E I S k value))
        (C3.complex3Scale
          (C3.realEmbed F (helicalEigenvalueMinus k))
          (Helical.helicalProjectorMinus E I S k value))

    helicityPerturbedMultiplierEigenvaluesPlus :
      (k : Z3.FourierMode) →
      helicalEigenvaluePlus k
      ≡
      C3.add F
        (baseWeight k)
        (C3.multiply F
          (helicitySignScalar sign epsilon)
          (Helical.modeNorm S k))

    helicityPerturbedMultiplierEigenvaluesMinus :
      (k : Z3.FourierMode) →
      helicalEigenvalueMinus k
      ≡
      C3.add F
        (baseWeight k)
        (C3.negate F
          (C3.multiply F
            (helicitySignScalar sign epsilon)
            (Helical.modeNorm S k)))

    StrictlyPositive : C3.Carrier F → Set r
    _≤_ : C3.Carrier F → C3.Carrier F → Set r

    helicityPerturbedMultiplierStrictlyPositive :
      ∀ k → StrictlyPositive (helicalEigenvaluePlus k)
            × StrictlyPositive (helicalEigenvalueMinus k)

    lowerConstant upperConstant : C3.Carrier F

    helicityPerturbedMultiplierUniformLowerBound :
      ∀ k → _≤_ lowerConstant (helicalEigenvaluePlus k)

    helicityPerturbedMultiplierUniformUpperBound :
      ∀ k → _≤_ (helicalEigenvaluePlus k) upperConstant

    helicityPerturbedQEvenRealityCompatible :
      (k : Z3.FourierMode) (value : C3.Complex3 F) →
      C3.Carrier F

    helicityPerturbedQControlsHsUniformly :
      (N : Nat) (velocity : Velocity F) → C3.Carrier F

open HelicityPerturbedCandidateLaws public

record GlobalHelicityDerivativeSplit
    {r : Level} (F : C3.RealField r) : Set (lsuc r) where
  field
    baseQuadraticReserve helicityDissipationCorrection
      perturbedQuadraticReserve baseCubicContribution
      perturbedCubicContribution quarticReserve : C3.Carrier F

    helicityPerturbedQuadraticLinearDerivative :
      perturbedQuadraticReserve
      ≡ C3.add F baseQuadraticReserve helicityDissipationCorrection

    globalHelicityPerturbationNonlinearDerivativeVanishes :
      perturbedCubicContribution ≡ baseCubicContribution

    helicityPerturbedQuadraticNonlinearDerivativeReduction :
      perturbedCubicContribution ≡ baseCubicContribution

    helicityPerturbedQuadraticReserveFormula :
      perturbedQuadraticReserve
      ≡ C3.add F baseQuadraticReserve helicityDissipationCorrection

    helicityPerturbedCubicContributionFormula :
      perturbedCubicContribution ≡ baseCubicContribution

    helicityPerturbedQuarticReserveFormula :
      quarticReserve ≡ quarticReserve

open GlobalHelicityDerivativeSplit public

helicityPerturbedQuarticExactDegreeSplit :
  ∀ {r} {F : C3.RealField r}
    (D : GlobalHelicityDerivativeSplit F) →
  perturbedCubicContribution D ≡ baseCubicContribution D
helicityPerturbedQuarticExactDegreeSplit D =
  globalHelicityPerturbationNonlinearDerivativeVanishes D

operatorQuadraticCarrierImplemented : Bool
operatorQuadraticCarrierImplemented = true

operatorQuadraticCarrierImplementedIsTrue :
  operatorQuadraticCarrierImplemented ≡ true
operatorQuadraticCarrierImplementedIsTrue = refl

helicityPerturbedUniformPositivityClosed : Bool
helicityPerturbedUniformPositivityClosed = false

helicityPerturbedUniformPositivityClosedIsFalse :
  helicityPerturbedUniformPositivityClosed ≡ false
helicityPerturbedUniformPositivityClosedIsFalse = refl
