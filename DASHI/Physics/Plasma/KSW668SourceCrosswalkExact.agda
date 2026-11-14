module DASHI.Physics.Plasma.KSW668SourceCrosswalkExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Plasma.MHDFullTransferFromExchangeCompatiblePayloadExact as MHD
import DASHI.Physics.Plasma.MHDLiteralIdealInvariantTriadCompilerExact as Invariants
import DASHI.Physics.Plasma.KSW668FiniteDiscriminatorsExact as Finite
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as U1
import DASHI.Physics.Electromagnetism.RightHandRule369Exact as Orientation
import DASHI.Physics.Chemistry.AtomicPeriodicTable369HydrogenReducedMassExact as Hydrogen
import DASHI.Quantum.QuantumMereologySpacetimePromotionExact as Spacetime

------------------------------------------------------------------------
-- KSW 668: exact OWNER reuse.  Do not copy original mathematical proofs,
-- infer a numerical law from a type, or merge distinct physical carriers.
------------------------------------------------------------------------

originalPairCancellation :
  ∀ {r} {F : C3.RealField r}
    (x : MHD.ExchangeCompatibleTransfer F) →
  C3.add F (MHD.forwardTransfer x) (MHD.reverseTransfer x)
  ≡ C3.zero F
originalPairCancellation = MHD.pairTransferCancels

originalPlasmaTriadBoundary :
  Invariants.IdealInvariantCompilerBoundary
originalPlasmaTriadBoundary =
  Invariants.canonicalIdealInvariantCompilerBoundary

originalU1Boundary : U1.U1ElectromagneticBoundary
originalU1Boundary = U1.canonicalU1ElectromagneticBoundary

original369PoyntingOrientation : Orientation.RightHandRule369Boundary
original369PoyntingOrientation =
  Orientation.canonicalRightHandRule369Boundary

original369HydrogenReducedMass : Hydrogen.ReducedMassExecutionReceipt
original369HydrogenReducedMass =
  Hydrogen.canonicalReducedMassExecutionReceipt

original369HydrogenCorrectionBudget : Hydrogen.HydrogenCorrectionBudget
original369HydrogenCorrectionBudget =
  Hydrogen.canonicalHydrogenCorrectionBudget

originalQuantumSpacetimeBoundary :
  Spacetime.QuantumMereologySpacetimeBoundary
originalQuantumSpacetimeBoundary =
  Spacetime.canonicalQuantumMereologySpacetimeBoundary

------------------------------------------------------------------------
-- Source-indexed physical gates, not fictitious inhabitants.
------------------------------------------------------------------------

record KSW668PhysicalObligations : Set where
  constructor ksw668-physical-obligations
  field
    actualMaxwellVectorFieldAndConstitutiveOwner : String
    localDifferentialPoyntingDerivation : String
    integratedBoundaryFluxAndRegularity : String
    calibratedNuclearRatesAndQValues : String
    sameSampleCarbonIsotopeAcquisition : String
    sameObjectLorentzKKMetricCausalCone : String
    controllableTransportAndArrivalMeasurement : String
    biologicalInterventionConfounderControls : String
    originalCrossPRSourceLineage : String

canonicalUnpaidPhysicalObligations : KSW668PhysicalObligations
canonicalUnpaidPhysicalObligations = ksw668-physical-obligations
  "DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact: require actual E/B/J and medium"
  "Maxwell PDE plus vector calculus and local J dot E, not a finite cancellation theorem"
  "Poynting surface integral, domain/time regularity and observational boundary conditions"
  "C12 triple-alpha and C14 N14(n,p) channels: rates, Q values, plasma environment and competing products"
  "paired isotope mass spectrometry, background production, transport and chemical fractionation"
  "PR 1460 + PR 1248: same metric, physical cone, true 5D reduction and observer dynamics"
  "operational signalling/control, conserved stress and measured arrival; entanglement alone is not transport"
  "PR 1471: intervention, blinded controls, physiology and alternative metabolic redistribution"
  "PRs 1163/1248/1460/1503/1096/1126/1461/1471 remain separate until exact branch joins"

finiteNoGo : ((w : Finite.ExchangeWorld) →
  Finite.strongMagnitude w ≡ 2 →
  Finite.weakMagnitude w ≡ 1 →
  Finite.forward w ≡ Finite.outflow) → Finite.⊥
finiteNoGo = Finite.universalStrongToWeakFromPairCancellationNoGo
