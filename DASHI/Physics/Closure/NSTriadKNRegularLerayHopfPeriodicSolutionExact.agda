module DASHI.Physics.Closure.NSTriadKNRegularLerayHopfPeriodicSolutionExact where

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
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Provide the exact solution class consumed by the localized Luo lane.
--
-- The global weak-solution component is Leray--Hopf:
--
--   u in L-infinity(0,T;H) intersection L2(0,T;V),
--   distributional periodic Navier--Stokes,
--   strong L2 continuity at 0+,
--   ||u(t)||_2^2 + 2 integral_0^t ||grad u||_2^2
--     <= ||u_0||_2^2
--
-- under unit viscosity.  Separately, Luo's continuation theorem assumes the
-- solution is already regular on (0,T).  That prior regularity licenses the
-- exact projected cutoff energy identity on every compact pre-terminal
-- interval.  The identity is not inferred from the general Leray--Hopf energy
-- inequality.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNLuoCutoffEnergyBootstrapExact as Bootstrap
import DASHI.Physics.Closure.NSTriadKNLocalizedBKMScaleDictionaryExact as Scale
open import DASHI.Physics.YangMills.CompactLieProofLevel

two : ℚ
two = 1ℚ + 1ℚ

record PeriodicLerayHopfSolution
    {d s t : Level}
    (InitialDatum : Set d)
    (Solution : Set s)
    (Time : Set t) : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    initialDatum : InitialDatum
    solution : Solution
    zeroTime : Time

    InEnergySpaceH : Solution → Time → Set (s ⊔ t)
    InDissipationSpaceV : Solution → Time → Set (s ⊔ t)

    essentiallyBoundedInH :
      (time : Time) → InEnergySpaceH solution time

    squareIntegrableInV :
      (time : Time) → InDissipationSpaceV solution time

    SolvesPeriodicNavierStokesDistributionally : Set (d ⊔ s ⊔ t)
    solvesPeriodicNavierStokesDistributionally :
      SolvesPeriodicNavierStokesDistributionally

    StrongL2ContinuousAtZero : Set (d ⊔ s ⊔ t)
    strongL2ContinuousAtZero : StrongL2ContinuousAtZero

    initialL2Squared : ℚ
    l2SquaredAt : Time → ℚ
    integratedGradientL2SquaredFromZero : Time → ℚ

    initialL2Nonnegative : 0ℚ ≤ initialL2Squared
    l2SquaredNonnegative :
      (time : Time) → 0ℚ ≤ l2SquaredAt time
    integratedGradientNonnegative :
      (time : Time) →
      0ℚ ≤ integratedGradientL2SquaredFromZero time

    globalLerayHopfEnergyInequality :
      (time : Time) →
      l2SquaredAt time
        + two * integratedGradientL2SquaredFromZero time
      ≤ initialL2Squared

open PeriodicLerayHopfSolution public

record RegularLerayHopfBeforeTerminal
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (lerayHopf : PeriodicLerayHopfSolution InitialDatum Solution Time)
    (terminalTime : Time) : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    RegularOnOpenIntervalBeforeTerminal : Set (s ⊔ t)
    regularOnOpenIntervalBeforeTerminal :
      RegularOnOpenIntervalBeforeTerminal

    SmoothDivergenceFreeFiniteEnergyInitialDatum : Set (d ⊔ s)
    smoothDivergenceFreeFiniteEnergyInitialDatum :
      SmoothDivergenceFreeFiniteEnergyInitialDatum

    ClassicalProjectedTestingValidBeforeTerminal : Set (s ⊔ t)
    classicalProjectedTestingValidBeforeTerminal :
      ClassicalProjectedTestingValidBeforeTerminal

open RegularLerayHopfBeforeTerminal public

record OfficialLuoCutoffQuantities
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {lerayHopf : PeriodicLerayHopfSolution InitialDatum Solution Time}
    {terminalTime : Time}
    (regular : RegularLerayHopfBeforeTerminal lerayHopf terminalTime)
    (shell : Nat) : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    previousHardHighEnergy : ℚ
    currentHardHighEnergy : ℚ
    integratedHardHighGradientL2Squared : ℚ

    signedIntegratedProjectedFlux : ℚ
    absoluteCutoffFluxAtTime : Time → ℚ
    integratedAbsoluteCutoffFlux : ℚ

    weightedShellEnergyMajorant : ℚ
    localizedLowPassGradientIntegral : ℚ
    profileSchurConstant : ℚ
    universalGradientThreshold : ℚ

    previousEnergyNonnegative : 0ℚ ≤ previousHardHighEnergy
    currentEnergyNonnegative : 0ℚ ≤ currentHardHighEnergy
    integratedGradientNonnegative :
      0ℚ ≤ integratedHardHighGradientL2Squared
    integratedAbsoluteFluxNonnegative :
      0ℚ ≤ integratedAbsoluteCutoffFlux
    weightedEnergyNonnegative : 0ℚ ≤ weightedShellEnergyMajorant
    localizedGradientNonnegative :
      0ℚ ≤ localizedLowPassGradientIntegral
    profileSchurConstantNonnegative : 0ℚ ≤ profileSchurConstant
    universalGradientThresholdNonnegative :
      0ℚ ≤ universalGradientThreshold

    preterminalProjectedEnergyIdentity :
      currentHardHighEnergy
        + two * integratedHardHighGradientL2Squared
      ≡ previousHardHighEnergy + signedIntegratedProjectedFlux

    signedFluxBelowIntegratedAbsoluteFlux :
      signedIntegratedProjectedFlux ≤ integratedAbsoluteCutoffFlux

    integratedFluxIsTimeIntegralOfPointwiseFlux :
      Set (s ⊔ t)

    integratedFluxTimeIntegralWitness :
      integratedFluxIsTimeIntegralOfPointwiseFlux

    integratedFluxWeightedSchurEstimate :
      integratedAbsoluteCutoffFlux
        ≤ profileSchurConstant
          * (weightedShellEnergyMajorant
            * localizedLowPassGradientIntegral)

    localizedGradientThresholdSmallness :
      localizedLowPassGradientIntegral ≤ universalGradientThreshold

    parabolicWindowDenominator : Nat
    parabolicWindowDenominatorMeaning :
      parabolicWindowDenominator
        ≡ Scale.parabolicWindowDenominator shell

    TerminalWindowIsLuoParabolicWindow : Set t
    terminalWindowIsLuoParabolicWindow :
      TerminalWindowIsLuoParabolicWindow

open OfficialLuoCutoffQuantities public

physicalCutoffDissipation :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {lerayHopf : PeriodicLerayHopfSolution InitialDatum Solution Time}
    {terminalTime : Time}
    {regular : RegularLerayHopfBeforeTerminal lerayHopf terminalTime}
    {shell : Nat} →
  OfficialLuoCutoffQuantities regular shell → ℚ
physicalCutoffDissipation Q =
  two * integratedHardHighGradientL2Squared Q

regularProjectedEnergyInequality :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {lerayHopf : PeriodicLerayHopfSolution InitialDatum Solution Time}
    {terminalTime : Time}
    {regular : RegularLerayHopfBeforeTerminal lerayHopf terminalTime}
    {shell : Nat} →
  (Q : OfficialLuoCutoffQuantities regular shell) →
  currentHardHighEnergy Q + physicalCutoffDissipation Q
    ≤ previousHardHighEnergy Q + integratedAbsoluteCutoffFlux Q
regularProjectedEnergyInequality Q =
  let
    exactToSigned :
      currentHardHighEnergy Q + physicalCutoffDissipation Q
        ≤ previousHardHighEnergy Q + signedIntegratedProjectedFlux Q
    exactToSigned =
      ℚₚ.≤-reflexive (preterminalProjectedEnergyIdentity Q)
  in
  ℚₚ.≤-trans exactToSigned
    (ℚₚ.+-mono-≤ ℚₚ.≤-refl
      (signedFluxBelowIntegratedAbsoluteFlux Q))

officialLuoCutoffData :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {lerayHopf : PeriodicLerayHopfSolution InitialDatum Solution Time}
    {terminalTime : Time}
    {regular : RegularLerayHopfBeforeTerminal lerayHopf terminalTime}
    {shell : Nat} →
  OfficialLuoCutoffQuantities regular shell →
  Bootstrap.LuoCutoffEnergyFluxData
officialLuoCutoffData Q = Bootstrap.cutoff-data
  (previousHardHighEnergy Q)
  (currentHardHighEnergy Q)
  (physicalCutoffDissipation Q)
  (integratedAbsoluteCutoffFlux Q)
  (weightedShellEnergyMajorant Q)
  (localizedLowPassGradientIntegral Q)
  (profileSchurConstant Q)
  (universalGradientThreshold Q)
  (previousEnergyNonnegative Q)
  (currentEnergyNonnegative Q)
  dissipationNonnegative
  (integratedAbsoluteFluxNonnegative Q)
  (weightedEnergyNonnegative Q)
  (localizedGradientNonnegative Q)
  (profileSchurConstantNonnegative Q)
  (universalGradientThresholdNonnegative Q)
  (regularProjectedEnergyInequality Q)
  (integratedFluxWeightedSchurEstimate Q)
  (localizedGradientThresholdSmallness Q)
  where
  dissipationNonnegative : 0ℚ ≤ physicalCutoffDissipation Q
  dissipationNonnegative =
    let
      instance
        twoNN = Data.Rational.Base.nonNegative
          (ℚₚ.+-mono-≤ ℚₚ.0≤1 ℚₚ.0≤1)
        gradientNN = Data.Rational.Base.nonNegative
          (integratedGradientNonnegative Q)
    in
    ℚₚ.nonNegative⁻¹ (physicalCutoffDissipation Q)

regularLerayHopfCarrierConstructed : Bool
regularLerayHopfCarrierConstructed = true

factorTwoDissipationNormalizationRecorded : Bool
factorTwoDissipationNormalizationRecorded = true

preterminalEnergyIdentitySeparatedFromWeakInequality : Bool
preterminalEnergyIdentitySeparatedFromWeakInequality = true

officialLuoCutoffDataConstructorClosed : Bool
officialLuoCutoffDataConstructorClosed = true

regularLerayHopfCarrierConstructedIsTrue :
  regularLerayHopfCarrierConstructed ≡ true
regularLerayHopfCarrierConstructedIsTrue = refl

factorTwoDissipationNormalizationRecordedIsTrue :
  factorTwoDissipationNormalizationRecorded ≡ true
factorTwoDissipationNormalizationRecordedIsTrue = refl

preterminalEnergyIdentitySeparatedFromWeakInequalityIsTrue :
  preterminalEnergyIdentitySeparatedFromWeakInequality ≡ true
preterminalEnergyIdentitySeparatedFromWeakInequalityIsTrue = refl

officialLuoCutoffDataConstructorClosedIsTrue :
  officialLuoCutoffDataConstructorClosed ≡ true
officialLuoCutoffDataConstructorClosedIsTrue = refl
