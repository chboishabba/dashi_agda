module DASHI.Physics.BoundaryScienceGeneralisationBridgesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Materials.NickelBaseSuperalloyMechanismExact as Superalloy
import DASHI.Physics.Nuclear.FissionInstrumentationControlReliabilityExact as FissionIC
import DASHI.Physics.Plasma.ReducedFluidKineticHermiteNumericsExact as ReducedPlasma
import DASHI.Physics.Accelerators.FlashRadiographyPhysicsExact as FlashRad
import DASHI.Chemistry.Spectroscopy.CryogenicMessengerTagActionSpectroscopyExact as CryoIR

import DASHI.Physics.RezaBurnResistantAlloyScienceExact as Reza
import DASHI.Physics.LeBlancFissionInstrumentationControlScienceExact as LeBlanc
import DASHI.Physics.Plasma.LoureiroViriatoNumericsScienceExact as Viriato
import DASHI.Physics.ScorpiusRadiographicAcceleratorScienceExact as Scorpius
import DASHI.Physics.MaiwaldActionSpectroscopyScienceExact as Maiwald

record GeneralisationBridge : Set where
  constructor generalisation-bridge
  field
    domainOwner : String
    caseOwner : String
    sharedMechanism : String
    caseSpecificResidual : String

open GeneralisationBridge public

rezaSuperalloyBridge : GeneralisationBridge
rezaSuperalloyBridge = generalisation-bridge
  "DASHI.Physics.Materials.NickelBaseSuperalloyMechanismExact"
  "DASHI.Physics.RezaBurnResistantAlloyScienceExact"
  "gamma/gamma-prime strengthening, oxidation-scale protection, processing -> microstructure -> property dependence"
  "exact Jacinto/Hardwick composition windows, source-stated element roles, burn-test/tensile examples and patent-specific fabrication details"

leblancFissionICBridge : GeneralisationBridge
leblancFissionICBridge = generalisation-bridge
  "DASHI.Physics.Nuclear.FissionInstrumentationControlReliabilityExact"
  "DASHI.Physics.LeBlancFissionInstrumentationControlScienceExact"
  "sensing, conditioning, estimation, protection, actuation, telemetry, harsh-environment qualification and reliability"
  "FSP/SNP FICS database, working-group and technology-growth-path receipts"

viriatoReducedPlasmaBridge : GeneralisationBridge
viriatoReducedPlasmaBridge = generalisation-bridge
  "DASHI.Physics.Plasma.ReducedFluidKineticHermiteNumericsExact"
  "DASHI.Physics.Plasma.LoureiroViriatoNumericsScienceExact"
  "strong-guide-field reduced equations, operator splitting, Fourier/Hermite discretisation, closure and convergence obligations"
  "the exact KREHM/KRMHD scheme choices and Viriato benchmark suite"

scorpiusFlashRadBridge : GeneralisationBridge
scorpiusFlashRadBridge = generalisation-bridge
  "DASHI.Physics.Accelerators.FlashRadiographyPhysicsExact"
  "DASHI.Physics.ScorpiusRadiographicAcceleratorScienceExact"
  "electron-beam induction acceleration, bremsstrahlung conversion, transmission imaging, blur/noise and inverse inference"
  "DARHT/Scorpius architecture and programme-specific pulse/radiography context"

maiwaldCryoIRBridge : GeneralisationBridge
maiwaldCryoIRBridge = generalisation-bridge
  "DASHI.Chemistry.Spectroscopy.CryogenicMessengerTagActionSpectroscopyExact"
  "DASHI.Physics.MaiwaldActionSpectroscopyScienceExact"
  "cryogenic ion trapping, messenger tagging, resonant tag predissociation, mass selection and spectrum-to-structure assignment"
  "JPL SURP valine/aminovaleric-acid experiment, stated messenger implementation and mission biosignature application"

record GeneralisationBoundary : Set where
  constructor generalisation-boundary
  field
    caseSourceFactDefinesDomainLaw : Bool
    caseSourceFactDefinesDomainLawIsFalse : caseSourceFactDefinesDomainLaw ≡ false
    genericDomainLawErasesCaseProvenance : Bool
    genericDomainLawErasesCaseProvenanceIsFalse : genericDomainLawErasesCaseProvenance ≡ false
    sharedMechanismMeansSameEngineeringImplementation : Bool
    sharedMechanismMeansSameEngineeringImplementationIsFalse : sharedMechanismMeansSameEngineeringImplementation ≡ false

canonicalGeneralisationBoundary : GeneralisationBoundary
canonicalGeneralisationBoundary = generalisation-boundary
  false refl
  false refl
  false refl
