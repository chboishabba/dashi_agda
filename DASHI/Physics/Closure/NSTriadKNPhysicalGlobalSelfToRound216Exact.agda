module DASHI.Physics.Closure.NSTriadKNPhysicalGlobalSelfToRound216Exact where

------------------------------------------------------------------------
-- LITERAL GLOBAL SELF PAYMENT -> ROUND216 SELF/EXTERNAL COMPILER
--
-- The physical four-helicity theorem already proves, on one literal finite
-- Galerkin system,
--
--   N_self <= E D + E D.
--
-- Round216 wants the self owner in the form
--
--   N_self <= a_self D + F_self.
--
-- We choose
--
--   a_self = E + E,     F_self = 0,
--
-- and reuse the SAME physical dissipation D.  This file then accepts only the
-- remaining external-owner payment on that same D and constructs Round216's
-- complete split payment.  No cutoff factor, absolute value, positivity
-- observer, or surrogate self scalar is introduced.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNMHDRadiusReciprocalToNormalizedDirectionRound464Exact as R464
import DASHI.Physics.Closure.NSTriadKNPhysicalHHAndNestedRadiusCompilerRound468Exact as R468
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as R109
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalSelfFourHelicityEDPaymentExact as Self
import DASHI.Physics.Closure.NSTriadKNPackageASelfExternalSignedProductionCompilerRound216Exact as R216

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalSelfToRound216
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws
      F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S)
    (O : Leray.RationalInverseNormOrder
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem))
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem)
    (radiusCalibration :
      R464.PhysicalSquareAndMHDCalibration
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem)
        S)
    (orientation : R468.PhysicalRadiusOrientation S) where

  module Global = Self.GlobalSelfPayment
    physicalSystem S L O unitGap radiusCalibration orientation

  physicalEnergy : ℚ
  physicalEnergy = R109.sumEnergy Global.modalED Global.modes

  physicalDissipation : ℚ
  physicalDissipation =
    R109.sumDissipation Global.modalED Global.modes

  selfAbsorbedCoefficient : ℚ
  selfAbsorbedCoefficient = physicalEnergy + physicalEnergy

  selfPaymentRound216Form :
    Global.globalSelfPhase
    ≤ selfAbsorbedCoefficient * physicalDissipation + 0ℚ
  selfPaymentRound216Form =
    let
      raw = Global.globalSelfPhaseBelowTwoED
      endpoint :
        (physicalEnergy * physicalDissipation)
          + (physicalEnergy * physicalDissipation)
        ≡ selfAbsorbedCoefficient * physicalDissipation + 0ℚ
      endpoint = solve (physicalEnergy ∷ physicalDissipation ∷ [])
    in
    subst
      (Global.globalSelfPhase ≤_)
      endpoint
      raw

  record ExternalOwnerPayment216 : Set where
    constructor external-owner-payment-216
    field
      externalProduction216 : ℚ
      externalAbsorbed216 : ℚ
      externalRemainder216 : ℚ
      externalPayment216 :
        externalProduction216
        ≤ externalAbsorbed216 * physicalDissipation
          + externalRemainder216

  open ExternalOwnerPayment216 public

  globalSelfAndExternalBuildRound216 :
    ExternalOwnerPayment216 →
    R216.SplitSignedCriticalPayment
  globalSelfAndExternalBuildRound216 external = record
    { R216.criticalDissipation = physicalDissipation
    ; R216.selfProduction = Global.globalSelfPhase
    ; R216.externalProduction = externalProduction216 external
    ; R216.selfAbsorbed = selfAbsorbedCoefficient
    ; R216.externalAbsorbed = externalAbsorbed216 external
    ; R216.selfRemainder = 0ℚ
    ; R216.externalRemainder = externalRemainder216 external
    ; R216.selfPayment = selfPaymentRound216Form
    ; R216.externalPayment = externalPayment216 external
    }

  globalSelfAndExternalCombinedPayment :
    (external : ExternalOwnerPayment216) →
    R216.combinedProduction (globalSelfAndExternalBuildRound216 external)
    ≤
    R216.combinedAbsorbed (globalSelfAndExternalBuildRound216 external)
      * R216.criticalDissipation
          (globalSelfAndExternalBuildRound216 external)
      + R216.combinedRemainder
          (globalSelfAndExternalBuildRound216 external)
  globalSelfAndExternalCombinedPayment external =
    R216.selfExternalPaymentsCombine
      (globalSelfAndExternalBuildRound216 external)
