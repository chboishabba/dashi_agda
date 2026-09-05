module DASHI.Physics.RezaBurnResistantAlloyScienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificMechanismEvidenceBidiExact as S

data AlloyElement : Set where nickel cobalt chromium aluminum titanium carbon boron zirconium manganese : AlloyElement
data MetallurgicalRole : Set where burnResistance solidSolutionStrengthening oxidationResistance gammaPrimeStrengthening grainBoundaryStrengthening fabricationSupport : MetallurgicalRole

record CompositionRange : Set where
  constructor composition-range
  field element : AlloyElement; minWeightPercent : Nat; maxWeightPercent : Nat
open CompositionRange public
nickelRange = composition-range nickel 55 75
cobaltRange = composition-range cobalt 12 17
chromiumRange = composition-range chromium 4 16
aluminumRange = composition-range aluminum 1 4
titaniumRange = composition-range titanium 1 4

record ElementMechanism : Set where
  constructor element-mechanism
  field element : AlloyElement; role : MetallurgicalRole; sourceReference : String; boundedReading : String
open ElementMechanism public

nickelBurnMechanism = element-mechanism nickel burnResistance "US20030053926A1 paras 18-20" "High nickel fraction is identified as the primary burn-resistance design feature."
cobaltStrengthMechanism = element-mechanism cobalt solidSolutionStrengthening "US20030053926A1 para 21" "Cobalt is described as a solid-solution strengthener in the nickel matrix while retaining burn resistance."
chromiumOxidationMechanism = element-mechanism chromium oxidationResistance "US20030053926A1 para 22" "Chromium is included for oxidation resistance while maintaining burn resistance."
aluminumGammaPrimeMechanism = element-mechanism aluminum gammaPrimeStrengthening "US20030053926A1 para 23" "Aluminum contributes oxidation resistance and gamma-prime strengthening."
titaniumGammaPrimeMechanism = element-mechanism titanium gammaPrimeStrengthening "US20030053926A1 para 24" "Titanium contributes to gamma-prime strengthening."

record AlloyProcess : Set where
  constructor alloy-process
  field firstMelt : String; secondMelt : String; downstreamWorking : String; sourceReference : String
canonicalAlloyProcess = alloy-process "vacuum induction melting" "vacuum arc remelting" "mechanical working into billet/bar/sheet/plate" "US20030053926A1 para 26"

burnStrengthTradeoff : S.ScientificMechanismReceipt
burnStrengthTradeoff = S.scientific-mechanism-receipt "Jacinto-Hardwick nickel superalloy family" "simultaneous high-pressure-oxygen burn resistance and high tensile strength for rocket-engine preburner/turbomachinery service" S.constitutiveOrEngineeringMechanism S.sourceBacked "US20030053926A1" "This is a multi-objective materials design problem; either property alone is insufficient."

gammaPrimeBoundary : S.ScientificMechanismReceipt
gammaPrimeBoundary = S.scientific-mechanism-receipt "Ni-Al-Ti strengthening" "Al and Ti additions support gamma-prime precipitation strengthening" S.constitutiveOrEngineeringMechanism S.sourceBacked "US20030053926A1 paras 23-24" "The patent identifies the mechanism qualitatively; phase fraction, precipitate size and heat-treatment dependence remain unresolved."

alloyNeedsMicrostructureReceipt : S.ScientificReverseObligation
alloyNeedsMicrostructureReceipt = S.scientific-reverse-obligation "Jacinto-Hardwick alloy mechanism" S.constitutiveParameterReceipt "recover heat treatment, gamma-prime volume fraction/size, grain size, phase stability and oxygen-exposure microstructure" "a microstructure-resolved strength/burn-resistance explanation" "complete mechanistic sufficiency merely from nominal composition"

record CurrentRezaAlloyScienceAssessment : Set where
  constructor current-reza-alloy-science-assessment
  field compositionWindowOwned : Bool; compositionWindowOwnedIsTrue : compositionWindowOwned ≡ true; elementRolesOwned : Bool; elementRolesOwnedIsTrue : elementRolesOwned ≡ true; fabricationSequenceOwned : Bool; fabricationSequenceOwnedIsTrue : fabricationSequenceOwned ≡ true; fullMicrostructurePropertyModelOwned : Bool; fullMicrostructurePropertyModelOwnedIsFalse : fullMicrostructurePropertyModelOwned ≡ false
canonicalCurrentRezaAlloyScienceAssessment = current-reza-alloy-science-assessment true refl true refl true refl false refl
