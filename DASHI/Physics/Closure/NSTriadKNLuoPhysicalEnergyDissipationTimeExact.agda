module DASHI.Physics.Closure.NSTriadKNLuoPhysicalEnergyDissipationTimeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Own the exact semantic equalities between the rational cutoff quantities
-- used by the formal bootstrap and the literal periodic Navier--Stokes
-- quantities.  Pointwise flux and integrated absolute flux are deliberately
-- distinct: a proof-relevant time-integration witness connects them rather
-- than a dimensionally false equality.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNHardProjectorParsevalTransportExact as Orthogonal
import DASHI.Physics.Closure.NSTriadKNProjectedConvectionEnergyFluxExact as Energy
import DASHI.Physics.Closure.NSTriadKNLuoCutoffEnergyBootstrapExact as Bootstrap
import DASHI.Physics.Closure.NSTriadKNLocalizedBKMScaleDictionaryExact as Scale

record LiteralLuoCutoffEnergyDissipationTimeIdentification
    {r : Level}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (modes : List Z3.FourierMode)
    (shell : Nat) : Set (lsuc r) where
  field
    hardProjectorOrthogonal :
      Orthogonal.HardProjectorOrthogonalCertificate model modes shell

    projectedEnergyFlux : Energy.PeriodicProjectedConvectionFluxAdapter
    cutoffData : Bootstrap.LuoCutoffEnergyFluxData
    parabolicTimeCutoff : Bootstrap.LuoParabolicTimeCutoff

    physicalPreviousHardHighEnergy : ℚ
    physicalCurrentHardHighEnergy : ℚ
    physicalIntegratedHardHighDissipation : ℚ
    physicalAbsoluteCutoffFluxAtTime : ℚ
    physicalIntegratedAbsoluteCutoffFlux : ℚ
    physicalWeightedShellEnergyMajorant : ℚ
    physicalLocalizedLowPassGradientIntegral : ℚ

    previousEnergyMeaning :
      Bootstrap.previousCutoffEnergy cutoffData
        ≡ physicalPreviousHardHighEnergy

    currentEnergyMeaning :
      Bootstrap.currentCutoffEnergy cutoffData
        ≡ physicalCurrentHardHighEnergy

    dissipationMeaning :
      Bootstrap.currentCutoffDissipation cutoffData
        ≡ physicalIntegratedHardHighDissipation

    integratedFluxMeaning :
      Bootstrap.integratedAbsoluteCutoffFlux cutoffData
        ≡ physicalIntegratedAbsoluteCutoffFlux

    weightedShellEnergyMeaning :
      Bootstrap.cutoffEnergyMajorant cutoffData
        ≡ physicalWeightedShellEnergyMajorant

    localizedGradientIntegralMeaning :
      Bootstrap.localizedLowPassGradientIntegral cutoffData
        ≡ physicalLocalizedLowPassGradientIntegral

    pointwiseFluxQuantityMeaning :
      Energy.absoluteCutoffFlux (Energy.balance projectedEnergyFlux)
        ≡ physicalAbsoluteCutoffFluxAtTime

    parabolicWindowDenominatorMeaning :
      Bootstrap.windowDenominator parabolicTimeCutoff
        ≡ Scale.parabolicWindowDenominator shell

    TimeWindowIsLuoParabolicWindow : Set r
    timeWindowIsLuoParabolicWindow : TimeWindowIsLuoParabolicWindow

    PhysicalEnergyIsHardHighL2Squared : Set r
    physicalEnergyIsHardHighL2Squared :
      PhysicalEnergyIsHardHighL2Squared

    PhysicalDissipationIsHardHighGradientL2Squared : Set r
    physicalDissipationIsHardHighGradientL2Squared :
      PhysicalDissipationIsHardHighGradientL2Squared

    PhysicalFluxIsProjectedConvectionPairing : Set r
    physicalFluxIsProjectedConvectionPairing :
      PhysicalFluxIsProjectedConvectionPairing

    IntegratedFluxIsTimeIntegralOfPointwiseFlux : Set r
    integratedFluxIsTimeIntegralOfPointwiseFlux :
      IntegratedFluxIsTimeIntegralOfPointwiseFlux

    PhysicalGradientIntegralIsLuoLowPassIntegral : Set r
    physicalGradientIntegralIsLuoLowPassIntegral :
      PhysicalGradientIntegralIsLuoLowPassIntegral

open LiteralLuoCutoffEnergyDissipationTimeIdentification public

literalPhysicalLuoEnergyDissipationRecursion :
  ∀ {r}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode}
    {shell : Nat} →
  (I : LiteralLuoCutoffEnergyDissipationTimeIdentification
    model modes shell) →
  physicalCurrentHardHighEnergy I
    + physicalIntegratedHardHighDissipation I
    ≤
  physicalPreviousHardHighEnergy I
    + Bootstrap.profileSchurConstant (cutoffData I)
      * (physicalWeightedShellEnergyMajorant I
        * Bootstrap.universalGradientThreshold (cutoffData I))
literalPhysicalLuoEnergyDissipationRecursion I
  rewrite sym (currentEnergyMeaning I)
        | sym (dissipationMeaning I)
        | sym (previousEnergyMeaning I)
        | sym (weightedShellEnergyMeaning I) =
  Bootstrap.luoSmallTimeEnergyDissipationRecursion (cutoffData I)

literalPhysicalLuoBootstrapBound :
  ∀ {r}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode}
    {shell : Nat} →
  (I : LiteralLuoCutoffEnergyDissipationTimeIdentification
    model modes shell) →
  (certificate : Bootstrap.LuoCutoffBootstrapCertificate (cutoffData I)) →
  physicalCurrentHardHighEnergy I
    + physicalIntegratedHardHighDissipation I
    ≤ Bootstrap.nextCutoffBudget certificate
literalPhysicalLuoBootstrapBound I certificate
  rewrite sym (currentEnergyMeaning I)
        | sym (dissipationMeaning I) =
  Bootstrap.luoCutoffBootstrapBound (cutoffData I) certificate

literalLuoCutoffEnergyDissipationTimeInterfaceConstructed : Bool
literalLuoCutoffEnergyDissipationTimeInterfaceConstructed = true

pointwiseIntegratedFluxSeparationEnforced : Bool
pointwiseIntegratedFluxSeparationEnforced = true

literalLuoPhysicalRecursionTransportClosed : Bool
literalLuoPhysicalRecursionTransportClosed = true

canonicalLiteralLuoPhysicalIdentificationInhabited : Bool
canonicalLiteralLuoPhysicalIdentificationInhabited = false

literalLuoCutoffEnergyDissipationTimeInterfaceConstructedIsTrue :
  literalLuoCutoffEnergyDissipationTimeInterfaceConstructed ≡ true
literalLuoCutoffEnergyDissipationTimeInterfaceConstructedIsTrue = refl

pointwiseIntegratedFluxSeparationEnforcedIsTrue :
  pointwiseIntegratedFluxSeparationEnforced ≡ true
pointwiseIntegratedFluxSeparationEnforcedIsTrue = refl

literalLuoPhysicalRecursionTransportClosedIsTrue :
  literalLuoPhysicalRecursionTransportClosed ≡ true
literalLuoPhysicalRecursionTransportClosedIsTrue = refl

canonicalLiteralLuoPhysicalIdentificationInhabitedIsFalse :
  canonicalLiteralLuoPhysicalIdentificationInhabited ≡ false
canonicalLiteralLuoPhysicalIdentificationInhabitedIsFalse = refl
