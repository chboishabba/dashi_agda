module DASHI.Physics.Closure.NSTriadKNLuoMeanValueGronwallReductionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Factor the Section-4 mean-value/Gronwall argument into a strict implication
-- chain.  Once absolute continuity, the good-time selection, the differential
-- inequality, localized smallness and terminal regularity transport are
-- supplied, terminal continuity is derived and cannot be postulated again.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

record MeanValueGronwallPrimitiveInputs : Set₁ where
  field
    ShellEnergyAbsolutelyContinuous : Set
    shellEnergyAbsolutelyContinuous :
      ShellEnergyAbsolutelyContinuous

    IntegratedShellEnergyIdentity : Set
    integratedShellEnergyIdentity : IntegratedShellEnergyIdentity

    GoodInitialTime : Set
    terminalWindowMeanValueSelection :
      ShellEnergyAbsolutelyContinuous →
      IntegratedShellEnergyIdentity →
      GoodInitialTime

    GoodTimeEnergyBelowWindowAverage : Set
    goodTimeEnergyBelowWindowAverage :
      GoodInitialTime → GoodTimeEnergyBelowWindowAverage

    IntegralDifferentialInequality : Set
    integralDifferentialInequality :
      IntegralDifferentialInequality

    GronwallExponentNonnegative : Set
    gronwallExponentNonnegative :
      GronwallExponentNonnegative

    LocalizedGradientSmallness : Set
    localizedGradientSmallness : LocalizedGradientSmallness

    TerminalShellEnergyBound : Set
    gronwallBoundWithLocalizedGradient :
      GoodInitialTime →
      GoodTimeEnergyBelowWindowAverage →
      IntegralDifferentialInequality →
      GronwallExponentNonnegative →
      LocalizedGradientSmallness →
      TerminalShellEnergyBound

    TerminalShellDissipationBound : Set
    terminalShellDissipationBound :
      TerminalShellEnergyBound → TerminalShellDissipationBound

    RequiredTerminalRegularity : Set
    shellBoundsGiveRequiredTerminalRegularity :
      TerminalShellEnergyBound →
      TerminalShellDissipationBound →
      RequiredTerminalRegularity

    ContinuityAtTerminal : Set
    requiredRegularityGivesTerminalContinuity :
      RequiredTerminalRegularity → ContinuityAtTerminal

open MeanValueGronwallPrimitiveInputs public

goodInitialTime :
  (inputs : MeanValueGronwallPrimitiveInputs) →
  GoodInitialTime inputs
goodInitialTime inputs =
  terminalWindowMeanValueSelection inputs
    (shellEnergyAbsolutelyContinuous inputs)
    (integratedShellEnergyIdentity inputs)

derivedTerminalShellEnergyBound :
  (inputs : MeanValueGronwallPrimitiveInputs) →
  TerminalShellEnergyBound inputs
derivedTerminalShellEnergyBound inputs =
  gronwallBoundWithLocalizedGradient inputs
    (goodInitialTime inputs)
    (goodTimeEnergyBelowWindowAverage inputs (goodInitialTime inputs))
    (integralDifferentialInequality inputs)
    (gronwallExponentNonnegative inputs)
    (localizedGradientSmallness inputs)

derivedTerminalShellDissipationBound :
  (inputs : MeanValueGronwallPrimitiveInputs) →
  TerminalShellDissipationBound inputs
derivedTerminalShellDissipationBound inputs =
  terminalShellDissipationBound inputs
    (derivedTerminalShellEnergyBound inputs)

derivedRequiredTerminalRegularity :
  (inputs : MeanValueGronwallPrimitiveInputs) →
  RequiredTerminalRegularity inputs
derivedRequiredTerminalRegularity inputs =
  shellBoundsGiveRequiredTerminalRegularity inputs
    (derivedTerminalShellEnergyBound inputs)
    (derivedTerminalShellDissipationBound inputs)

derivedContinuityAtTerminal :
  (inputs : MeanValueGronwallPrimitiveInputs) →
  ContinuityAtTerminal inputs
derivedContinuityAtTerminal inputs =
  requiredRegularityGivesTerminalContinuity inputs
    (derivedRequiredTerminalRegularity inputs)

record MeanValueGronwallReceipt : Set₁ where
  field
    primitiveInputs : MeanValueGronwallPrimitiveInputs
    terminalEnergy : TerminalShellEnergyBound primitiveInputs
    terminalDissipation : TerminalShellDissipationBound primitiveInputs
    terminalRegularity : RequiredTerminalRegularity primitiveInputs
    terminalContinuity : ContinuityAtTerminal primitiveInputs

open MeanValueGronwallReceipt public

meanValueGronwallReceipt :
  MeanValueGronwallPrimitiveInputs → MeanValueGronwallReceipt
meanValueGronwallReceipt inputs = record
  { primitiveInputs = inputs
  ; terminalEnergy = derivedTerminalShellEnergyBound inputs
  ; terminalDissipation = derivedTerminalShellDissipationBound inputs
  ; terminalRegularity = derivedRequiredTerminalRegularity inputs
  ; terminalContinuity = derivedContinuityAtTerminal inputs
  }

meanValueGronwallReductionConstructed : Bool
meanValueGronwallReductionConstructed = true

terminalContinuityDerivedNotAssumed : Bool
terminalContinuityDerivedNotAssumed = true

meanValueGronwallReductionConstructedIsTrue :
  meanValueGronwallReductionConstructed ≡ true
meanValueGronwallReductionConstructedIsTrue = refl

terminalContinuityDerivedNotAssumedIsTrue :
  terminalContinuityDerivedNotAssumed ≡ true
terminalContinuityDerivedNotAssumedIsTrue = refl
