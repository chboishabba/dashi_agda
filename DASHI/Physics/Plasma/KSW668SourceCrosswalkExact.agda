module DASHI.Physics.Plasma.KSW668SourceCrosswalkExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (_+_)
import Data.Rational.Base as ℚ

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Plasma.MHDFullTransferFromExchangeCompatiblePayloadExact as MHD
import DASHI.Physics.Plasma.MHDLiteralIdealInvariantTriadCompilerExact as Invariants
import DASHI.Physics.Plasma.KSW668FiniteDiscriminatorsExact as Finite
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as U1
import DASHI.Physics.Electromagnetism.RightHandRule369Exact as Orientation
import DASHI.Physics.Chemistry.AtomicPeriodicTable369HydrogenReducedMassExact as Hydrogen
import DASHI.Quantum.QuantumMereologySpacetimePromotionExact as Spacetime
import DASHI.Quantum.EntanglementGeometryMereologyBridgeExact as Entanglement
import DASHI.Physics.Closure.FormalCompressionUniversalityBridge as PostEntropy
import DASHI.Physics.Gravity.PenroseGlobalCausalityAuthorityExact as GlobalCausality
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MadelungPeriodPartitionExact as Madelung
import DASHI.Biology.EpigeneticBodyMemoryBridge as BodyMemory
import DASHI.Biology.KSW668EmpiricalIsotopeMagnetoreceptionSourceExact as EmpiricalBiology
import DASHI.Biology.KSW668HumanCarbon14ObservedExact as HumanAMS
import DASHI.Physics.Plasma.KSW668EmpiricalBoundariesExact as Empirical
import DASHI.Physics.Plasma.KSW668FullVectorMaxwellJetExact as VectorMaxwell
import DASHI.Physics.Gravity.KSW668KaluzaKleinSpacelikeFiberCausalExact as KK
import DASHI.Physics.Chemistry.KSW668NuclearElectronStateLedgerExact as Nuclear

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

originalEntanglementSpatialGeometryBoundary :
  Entanglement.EntanglementGeometryBoundary
originalEntanglementSpatialGeometryBoundary =
  Entanglement.canonicalEntanglementGeometryBoundary

originalPostEntropyMDLBoundary :
  PostEntropy.FormalCompressionBridgeBoundary
originalPostEntropyMDLBoundary =
  PostEntropy.canonicalFormalCompressionBridgeBoundary

originalGlobalCausalityAuthority :
  GlobalCausality.GlobalCausalityAuthorityReceipt
originalGlobalCausalityAuthority =
  GlobalCausality.canonicalGlobalCausalityAuthorityReceipt

original369MadelungBoundary :
  Madelung.MadelungPeriodPartitionBoundary
original369MadelungBoundary =
  Madelung.canonicalMadelungPeriodPartitionBoundary

originalBiologicalCausalityGuard :
  BodyMemory.EpigeneticBodyMemoryGuard
originalBiologicalCausalityGuard =
  BodyMemory.NoCausalityClosureClaim


-- B1: reuse the same original RealField full three-vector curl-jet theorem.
-- The existence of an analytic physical U1 continuum field remains separate.
originalFull3DMaxwellPoynting :
  ∀ {r} {F : C3.RealField r}
    (j : VectorMaxwell.FullVectorMaxwellJet F) →
  VectorMaxwell.fullVectorSignedBudget j ≡ C3.zero F
originalFull3DMaxwellPoynting =
  VectorMaxwell.fullVectorMaxwellPoyntingIdentity


-- D1/D2 standard spacelike-fibre KK projection theorem, not an
-- Einstein-matter field-equation solution and not exotic operational FTL.
originalSpacelikeKaluzaKleinProjectedCausal :
  (v : KK.SpacelikeKaluzaKleinCausalTangent) →
  KK.baseLorentzIntervalSquared v
    ℚ.≤ ℚ.0ℚ
originalSpacelikeKaluzaKleinProjectedCausal =
  KK.originalKaluzaKleinCausalProjection

-- C1 preserve all original NIST electrons across microscopic final-state
-- alternatives. Stronger physical scattering amplitudes remain unproved.
originalNuclearNeutralElectrons :
  Nuclear.electronInventoryMatches Nuclear.neutralDaughters
originalNuclearNeutralElectrons = Nuclear.neutralElectronReceipt

originalNuclearIonAndFreeElectronChannel :
  Nuclear.electronInventoryMatches
    Nuclear.ionAndFreeElectronDaughters
originalNuclearIonAndFreeElectronChannel =
  Nuclear.ionPlusElectronReceipt

originalNuclearBareQCorrection :
  Nuclear.atomicNeutralChannelQ
    + Nuclear.nuclearMinusAtomicBindingCorrection
    ≡ Nuclear.bareNuclearChannelQ
originalNuclearBareQCorrection =
  Nuclear.originalBareNuclearQCorrection

originalHumanAMSObservedDonor24 :
  HumanAMS.pMCHundredths HumanAMS.donor24Tendon
  ≡ HumanAMS.pMCHundredths HumanAMS.donor24Muscle + 2575
originalHumanAMSObservedDonor24 =
  HumanAMS.donor24MeasuredDifferentTissue14C

originalHumanAMSObservedDonor26 :
  HumanAMS.pMCHundredths HumanAMS.donor26Tendon
  ≡ HumanAMS.pMCHundredths HumanAMS.donor26Muscle + 3869
originalHumanAMSObservedDonor26 =
  HumanAMS.donor26MeasuredDifferentTissue14C

originalCrossLaneEmpiricalSourceStatus :
  Empirical.EmpiricalClosureGates
originalCrossLaneEmpiricalSourceStatus =
  Empirical.empiricalStatusAsOf20261114

publishedOriginalPigeonInterventionGroup :
  EmpiricalBiology.PublishedHomingGroup
publishedOriginalPigeonInterventionGroup = EmpiricalBiology.pigeonControl

publishedPigeonOvercastTotal :
  EmpiricalBiology.numberPigeons EmpiricalBiology.pigeonControl
  + EmpiricalBiology.numberPigeons EmpiricalBiology.pigeonDepleted ≡ 34
publishedPigeonOvercastTotal = EmpiricalBiology.publishedOvercastTotal

publishedSouthernHemisphere14CArchive :
  EmpiricalBiology.BiologicalArchiveAcquisition
publishedSouthernHemisphere14CArchive =
  EmpiricalBiology.originalSouthernPostbombAcquisition

publishedPigeonTranscriptomeArchive :
  EmpiricalBiology.BiologicalArchiveAcquisition
publishedPigeonTranscriptomeArchive =
  EmpiricalBiology.originalPigeonTranscriptomeRegistration

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
