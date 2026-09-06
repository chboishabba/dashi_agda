module DASHI.Physics.RezaBurnResistantAlloyScienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificMechanismEvidenceBidiExact as S

------------------------------------------------------------------------
-- JACINTO / HARDWICK BURN-RESISTANT NICKEL ALLOY SCIENCE
------------------------------------------------------------------------

data AlloyElement : Set where
  nickel cobalt chromium aluminum titanium carbon boron zirconium manganese
  : AlloyElement

data MetallurgicalRole : Set where
  burnResistance
  solidSolutionStrengthening
  oxidationResistance
  gammaPrimeStrengthening
  grainBoundaryStrengthening
  fabricationSupport
  : MetallurgicalRole

record CompositionRange : Set where
  constructor composition-range
  field
    element : AlloyElement
    minWeightPercent : Nat
    maxWeightPercent : Nat

open CompositionRange public

nickelRange : CompositionRange
nickelRange = composition-range nickel 55 75

cobaltRange : CompositionRange
cobaltRange = composition-range cobalt 12 17

chromiumRange : CompositionRange
chromiumRange = composition-range chromium 4 16

aluminumRange : CompositionRange
aluminumRange = composition-range aluminum 1 4

titaniumRange : CompositionRange
titaniumRange = composition-range titanium 1 4

record ElementMechanism : Set where
  constructor element-mechanism
  field
    element : AlloyElement
    role : MetallurgicalRole
    sourceReference : String
    boundedReading : String

open ElementMechanism public

nickelBurnMechanism : ElementMechanism
nickelBurnMechanism = element-mechanism nickel burnResistance
  "US20030053926A1 paras 18-20"
  "The patent attributes superior burn resistance primarily to the high nickel fraction and specifies at least 50 wt% Ni, with preferred embodiments around 70-75 wt%."

cobaltStrengthMechanism : ElementMechanism
cobaltStrengthMechanism = element-mechanism cobalt solidSolutionStrengthening
  "US20030053926A1 para 21"
  "Cobalt is described as a solid-solution strengthener in the nickel matrix while retaining burn resistance."

chromiumOxidationMechanism : ElementMechanism
chromiumOxidationMechanism = element-mechanism chromium oxidationResistance
  "US20030053926A1 para 22"
  "Chromium is included for oxidation resistance while maintaining burn resistance."

aluminumGammaPrimeMechanism : ElementMechanism
aluminumGammaPrimeMechanism = element-mechanism aluminum gammaPrimeStrengthening
  "US20030053926A1 para 23"
  "Aluminum contributes oxidation resistance and to the gamma-prime strengthening mechanism."

titaniumGammaPrimeMechanism : ElementMechanism
titaniumGammaPrimeMechanism = element-mechanism titanium gammaPrimeStrengthening
  "US20030053926A1 para 24"
  "Titanium contributes to gamma-prime strengthening."

record AlloyProcess : Set where
  constructor alloy-process
  field
    firstMelt : String
    secondMelt : String
    downstreamWorking : String
    sourceReference : String

canonicalAlloyProcess : AlloyProcess
canonicalAlloyProcess = alloy-process
  "vacuum induction melting"
  "vacuum arc remelting"
  "mechanical working of ingot into billet/bar/sheet/plate"
  "US20030053926A1 para 26"

burnStrengthTradeoff : S.ScientificMechanismReceipt
burnStrengthTradeoff = S.scientific-mechanism-receipt
  "Jacinto-Hardwick nickel superalloy family"
  "the design objective is simultaneous resistance to sustained combustion in high-pressure oxygen and sufficient tensile strength for rocket-engine preburner/turbomachinery structural service"
  S.constitutiveOrEngineeringMechanism
  S.sourceBacked
  "US20030053926A1 paras 1-4, 27-28 and claims"
  "This is a multi-objective materials design problem; high burn resistance alone or high tensile strength alone does not satisfy the stated engineering objective."

gammaPrimeBoundary : S.ScientificMechanismReceipt
gammaPrimeBoundary = S.scientific-mechanism-receipt
  "Ni-Al-Ti alloy strengthening"
  "Al and Ti additions are used to support gamma-prime precipitation strengthening in the nickel-base alloy"
  S.constitutiveOrEngineeringMechanism
  S.sourceBacked
  "US20030053926A1 paras 23-24"
  "The patent identifies the mechanism qualitatively; phase fraction, precipitate size distribution, heat-treatment dependence and full microstructural characterisation are not supplied by this receipt."

alloyNeedsMicrostructureReceipt : S.ScientificReverseObligation
alloyNeedsMicrostructureReceipt = S.scientific-reverse-obligation
  "Jacinto-Hardwick alloy performance mechanism"
  S.constitutiveParameterReceipt
  "recover heat treatment, gamma-prime volume fraction/size, grain size, phase stability and oxygen-exposure microstructure for tested examples"
  "a microstructure-resolved explanation of the strength/burn-resistance combination"
  "complete mechanistic sufficiency merely from nominal composition"

record CurrentRezaAlloyScienceAssessment : Set where
  constructor current-reza-alloy-science-assessment
  field
    compositionWindowOwned : Bool
    compositionWindowOwnedIsTrue : compositionWindowOwned ≡ true
    elementRolesOwned : Bool
    elementRolesOwnedIsTrue : elementRolesOwned ≡ true
    fabricationSequenceOwned : Bool
    fabricationSequenceOwnedIsTrue : fabricationSequenceOwned ≡ true
    fullMicrostructurePropertyModelOwned : Bool
    fullMicrostructurePropertyModelOwnedIsFalse :
      fullMicrostructurePropertyModelOwned ≡ false

canonicalCurrentRezaAlloyScienceAssessment : CurrentRezaAlloyScienceAssessment
canonicalCurrentRezaAlloyScienceAssessment = current-reza-alloy-science-assessment
  true refl
  true refl
  true refl
  false refl
