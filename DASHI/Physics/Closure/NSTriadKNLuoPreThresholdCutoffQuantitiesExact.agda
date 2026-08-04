module DASHI.Physics.Closure.NSTriadKNLuoPreThresholdCutoffQuantitiesExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Own the physical cutoff quantities before Luo's localized-gradient
-- smallness hypothesis is proved.  The historical OfficialLuoCutoffQuantities
-- record also contained a threshold and localizedGradientThresholdSmallness;
-- using it as physical input was circular.  This pre-threshold owner contains
-- the energy identity and flux estimate, but no criterion-sized budget.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNRegularLerayHopfPeriodicSolutionExact as LH
import DASHI.Physics.Closure.NSTriadKNLocalizedBKMScaleDictionaryExact as Scale

record PreThresholdLuoCutoffQuantities
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {lerayHopf : LH.PeriodicLerayHopfSolution InitialDatum Solution Time}
    {terminalTime : Time}
    (regular : LH.RegularLerayHopfBeforeTerminal lerayHopf terminalTime)
    (shell : Nat) : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    previousHardHighEnergy : ℚ
    currentHardHighEnergy : ℚ
    integratedHardHighGradientL2Squared : ℚ
    physicalDissipation : ℚ

    signedIntegratedProjectedFlux : ℚ
    absoluteCutoffFluxAtTime : Time → ℚ
    integratedAbsoluteCutoffFlux : ℚ

    weightedShellEnergyMajorant : ℚ
    localizedLowPassGradientIntegral : ℚ
    profileSchurConstant : ℚ

    previousEnergyNonnegative : 0ℚ ≤ previousHardHighEnergy
    currentEnergyNonnegative : 0ℚ ≤ currentHardHighEnergy
    integratedGradientNonnegative :
      0ℚ ≤ integratedHardHighGradientL2Squared
    physicalDissipationNonnegative : 0ℚ ≤ physicalDissipation
    integratedAbsoluteFluxNonnegative :
      0ℚ ≤ integratedAbsoluteCutoffFlux
    weightedEnergyNonnegative : 0ℚ ≤ weightedShellEnergyMajorant
    localizedGradientNonnegative :
      0ℚ ≤ localizedLowPassGradientIntegral
    profileSchurConstantNonnegative : 0ℚ ≤ profileSchurConstant

    physicalDissipationMeaning :
      physicalDissipation
      ≡ LH.two * integratedHardHighGradientL2Squared

    preterminalProjectedEnergyIdentity :
      currentHardHighEnergy + physicalDissipation
      ≡ previousHardHighEnergy + signedIntegratedProjectedFlux

    signedFluxBelowIntegratedAbsoluteFlux :
      signedIntegratedProjectedFlux ≤ integratedAbsoluteCutoffFlux

    IntegratedFluxIsTimeIntegralOfPointwiseFlux : Set (s ⊔ t)
    integratedFluxIsTimeIntegralOfPointwiseFlux :
      IntegratedFluxIsTimeIntegralOfPointwiseFlux

    integratedFluxWeightedSchurEstimate :
      integratedAbsoluteCutoffFlux
      ≤ profileSchurConstant
        * (weightedShellEnergyMajorant
          * localizedLowPassGradientIntegral)

    parabolicWindowDenominator : Nat
    parabolicWindowDenominatorMeaning :
      parabolicWindowDenominator
      ≡ Scale.parabolicWindowDenominator shell

    TerminalWindowIsLuoParabolicWindow : Set t
    terminalWindowIsLuoParabolicWindow :
      TerminalWindowIsLuoParabolicWindow

open PreThresholdLuoCutoffQuantities public

preThresholdProjectedEnergyInequality :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {lerayHopf : LH.PeriodicLerayHopfSolution InitialDatum Solution Time}
    {terminalTime : Time}
    {regular : LH.RegularLerayHopfBeforeTerminal lerayHopf terminalTime}
    {shell : Nat} →
  (Q : PreThresholdLuoCutoffQuantities regular shell) →
  currentHardHighEnergy Q + physicalDissipation Q
  ≤ previousHardHighEnergy Q + integratedAbsoluteCutoffFlux Q
preThresholdProjectedEnergyInequality Q
  rewrite preterminalProjectedEnergyIdentity Q =
  ℚₚ.+-mono-≤ ℚₚ.≤-refl
    (signedFluxBelowIntegratedAbsoluteFlux Q)

preThresholdCutoffCarrierConstructed : Bool
preThresholdCutoffCarrierConstructed = true

localizedThresholdAbsentFromPhysicalInput : Bool
localizedThresholdAbsentFromPhysicalInput = true

preThresholdCutoffCarrierConstructedIsTrue :
  preThresholdCutoffCarrierConstructed ≡ true
preThresholdCutoffCarrierConstructedIsTrue = refl

localizedThresholdAbsentFromPhysicalInputIsTrue :
  localizedThresholdAbsentFromPhysicalInput ≡ true
localizedThresholdAbsentFromPhysicalInputIsTrue = refl
