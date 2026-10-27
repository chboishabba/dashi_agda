module DASHI.Empirical.KozyrevMirrorClaimTesting where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Empirical.GRQuantumPredictionProtocol as PredictionProtocol
import DASHI.Promotion.CrossDomainClaimPromotionBoundary as ClaimBoundary
import DASHI.Physics.Foundations.TorqueTrialectic369Exact as Torque369
import DASHI.Physics.Closure.SignedZeroTorsionReceipt as SignedZero
import DASHI.Geometry.LorentzianLeviCivitaConditional as LeviCivita
import DASHI.Physics.YangMills.YangMillsCizekEinsteinCartanClaimAuditExact as EinsteinCartanAudit
import DASHI.Physics.YangMills.YangMillsPaperClaimAuditCarrierExact as PaperAudit
import DASHI.Core.ScientificMechanismEvidenceBidiExact as Science
import DASHI.Reasoning.TernaryPantsRecursiveWreathActionExact as ExistingWreath
import DASHI.Physics.Common.FiniteWreathRefinementExact as ExistingFiniteWreath
import DASHI.Topology.HelicalWeaveMappingTorusExact as ExistingHelix
import DASHI.Biology.DialecticalSheetSpiralExact as ExistingSpiral
import DASHI.Biology.Physical.Harmonic369HelixLiftExact as ExistingWinding
import DASHI.Interop.StationaryPhaseMirrorGratingToyReceipt as ExistingOptics
import DASHI.Physics.QuantumVacuum.PerfectConductorMaxwellSpectrumBidiExact as ExistingMaxwell
import DASHI.Physics.POAMSScientificMechanismBoundaryExact as POAMS

------------------------------------------------------------------------
-- Source-typed Kozyrev mirror claim intake. No new physical law.
--
-- The apparatus attributed to Kaznacheev/Trofimov is not S. V. Kozyrev's
-- p-adic wavelet construction. N. A. Kozyrev's historical time hypothesis
-- is also not an experimental validation of the later apparatus.
------------------------------------------------------------------------

data KozyrevReferent : Set where
  nikolaiHistoricalTimeHypothesis : KozyrevReferent
  kaznacheevTrofimovSpiralApparatus : KozyrevReferent
  sergeiPadicWaveletTheory : KozyrevReferent

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

apparatusNotPadicWavelets :
  kaznacheevTrofimovSpiralApparatus
  ≢ sergeiPadicWaveletTheory
apparatusNotPadicWavelets ()

apparatusNotHistoricalHypothesis :
  kaznacheevTrofimovSpiralApparatus
  ≢ nikolaiHistoricalTimeHypothesis
apparatusNotHistoricalHypothesis ()

data ClaimFamily : Set where
  apparatusGeometry : ClaimFamily
  ordinaryOpticalOrAcousticScattering : ClaimFamily
  subjectiveExperience : ClaimFamily
  physiologicalOrClinicalEffect : ClaimFamily
  remoteInformationTransfer : ClaimFamily
  clockOrCausalityAnomaly : ClaimFamily
  unbridgedKozyrevTorsionOrTimeEnergy : ClaimFamily

data EvidencePosture : Set where
  sourceDescribesDesign : EvidencePosture
  sourceReportsEffect : EvidencePosture
  externalToyModelOnly : EvidencePosture
  unoperationalisedClaim : EvidencePosture

record SourceTypedClaim : Set where
  constructor sourceTypedClaim
  field
    claimIdentifier : String
    family : ClaimFamily
    sourceAuthors : String
    sourceYear : Nat
    primaryRoot : String
    evidencePosture : EvidencePosture
    limitation : String

canonicalClaimIntake : List SourceTypedClaim
canonicalClaimIntake =
  sourceTypedClaim
    "KM-GEOM"
    apparatusGeometry
    "V. P. Kaznacheev; A. V. Trofimov"
    1998
    "RU2122446C1, filed 1996-07-02, published 1998-11-27"
    sourceDescribesDesign
    "Patent describes a spiral metal enclosure. Patent status does not establish any claimed treatment efficacy. English abstract says 0.5 mm; translated specification/claim says 1.5 mm; source conflict is open."
  ∷ sourceTypedClaim
    "KM-SCATTER"
    ordinaryOpticalOrAcousticScattering
    "Broken Branch, HI-1 and HI-12"
    2026
    "https://www.brokenbranch.dev/labs/as-seen-on-tv/honest-spiral/"
    externalToyModelOnly
    "Two-dimensional scalar/sound simulations do not establish three-dimensional apparatus effects or novel time physics."
  ∷ sourceTypedClaim
    "KM-SUBJECTIVE"
    subjectiveExperience
    "V. P. Kaznacheev"
    2002
    "https://www.physics.socionic.info/index.php/physics/article/view/267"
    sourceReportsEffect
    "Subjective reports require masked sham comparison and independent replication."
  ∷ sourceTypedClaim
    "KM-CLINICAL"
    physiologicalOrClinicalEffect
    "V. P. Kaznacheev; A. V. Trofimov"
    1998
    "https://patents.google.com/patent/RU2122446C1/en"
    sourceReportsEffect
    "Patent anecdotes are not randomised controlled treatment evidence. No clinical authority follows."
  ∷ sourceTypedClaim
    "KM-REMOTE"
    remoteInformationTransfer
    "V. P. Kaznacheev; A. V. Trofimov"
    2006
    "https://physics.socionic.info/index.php/physics/article/view/376"
    sourceReportsEffect
    "Reported information transfer needs precommitted random targets, recipient blinding, leakage control and independent replication."
  ∷ sourceTypedClaim
    "KM-TIME"
    clockOrCausalityAnomaly
    "Kozyrev mirror claims, as later recounted"
    2026
    "https://www.brokenbranch.dev/labs/as-seen-on-tv/does-the-mirror-focus/"
    unoperationalisedClaim
    "No calibrated clock anomaly or falsifiable time-energy measurand has been established by the cited model."
  ∷ sourceTypedClaim
    "KM-TORSION"
    unbridgedKozyrevTorsionOrTimeEnergy
    "Kozyrev mirror claims, as later recounted"
    2026
    "https://www.brokenbranch.dev/labs/as-seen-on-tv/does-the-mirror-focus/"
    unoperationalisedClaim
    "Related mechanical and Einstein-Cartan torsion is already formalised in DASHI. No same-object apparatus-to-geometric-torsion source, coupling, unit, calibration, null, or predicted effect is supplied yet."
  ∷ []

------------------------------------------------------------------------
-- Frozen, falsifiable experimental design obligations.
-- These are planned comparisons, not observations or measured effects.
------------------------------------------------------------------------

record TestTarget : Set where
  constructor testTarget
  field
    claimFamily : ClaimFamily
    observable : String
    activeAndShamComparison : String
    decisiveNegativeControl : String
    rejectionCondition : String

canonicalTestTargets : List TestTarget
canonicalTestTargets =
  testTarget
    ordinaryOpticalOrAcousticScattering
    "Frequency-resolved flux, field map, torque and uncertainty"
    "Matched spiral and matched non-spiral material controls"
    "Empty chamber, thermal equilibrium, numerical timestep/grid refinement"
    "Fail the specified effect threshold or show it also occurs in the sham"
  ∷ testTarget
    subjectiveExperience
    "Predeclared rating or behavioural score"
    "Randomised, masked active versus sham enclosure"
    "Expectancy, audio, light, temperature, airflow and order controls"
    "Held-out treatment contrast misses the preregistered threshold"
  ∷ testTarget
    physiologicalOrClinicalEffect
    "Predeclared validated physiological endpoint"
    "Ethics-approved randomised, blinded sham-controlled study"
    "Medication, resting period, selection and adverse-event controls"
    "No clinically meaningful effect after multiplicity correction"
  ∷ testTarget
    remoteInformationTransfer
    "Exact predeclared blinded-target hit rate"
    "Random, precommitted targets versus chance baseline"
    "Leak-proof target allocation, decoy sessions and auditor blinding"
    "Hit rate not distinguishable from prespecified chance baseline"
  ∷ testTarget
    clockOrCausalityAnomaly
    "Traceable synchronised clock difference and uncertainty"
    "Chamber versus matched sham and colocated reference clocks"
    "EM, thermal, vibration, pressure, timing-network and drift controls"
    "Any deviation lies within calibrated uncertainty"
  ∷ testTarget
    unbridgedKozyrevTorsionOrTimeEnergy
    "Existing torsion mathematics admitted; requested mirror-specific observable and units remain open"
    "Bridge under P4; instrument-only test may proceed separately"
    "Require a detector calibrated against known physical interactions"
    "Reject uninterpretable readings until a quantitative prediction exists"
  ∷ []

record ExperimentIntakeBoundary : Set where
  constructor experimentIntakeBoundary
  field
    claimsCatalogued : Bool
    claimsCataloguedIsTrue : claimsCatalogued ≡ true
    protocolIndependentlyPreregistered : Bool
    protocolIndependentlyPreregisteredIsFalse :
      protocolIndependentlyPreregistered ≡ false
    observationsSupplied : Bool
    observationsSuppliedIsFalse : observationsSupplied ≡ false
    independentlyReplicated : Bool
    independentlyReplicatedIsFalse : independentlyReplicated ≡ false
    empiricalPromotion : Bool
    empiricalPromotionIsFalse : empiricalPromotion ≡ false
    clinicalPromotion : Bool
    clinicalPromotionIsFalse : clinicalPromotion ≡ false

canonicalExperimentIntakeBoundary : ExperimentIntakeBoundary
canonicalExperimentIntakeBoundary =
  experimentIntakeBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

mirrorEmpiricalClaimBoundary :
  ClaimBoundary.CrossDomainPromotionExample
mirrorEmpiricalClaimBoundary =
  ClaimBoundary.mkBlockedExample
    "Mirror mechanism or source report is not verified physical efficacy"
    ClaimBoundary.structuralAnalogyClaim
    ClaimBoundary.empiricalFactClaim
    ClaimBoundary.measurementAuthorityBridgeReceipt
    ClaimBoundary.missingMeasurementAuthorityReason
    "Require frozen instrument calibration, controlled data, an independent replay and an explicit external authority review."

mirrorClinicalClaimBoundary :
  ClaimBoundary.CrossDomainPromotionExample
mirrorClinicalClaimBoundary =
  ClaimBoundary.mkBlockedExample
    "Patent and reported symptoms are not clinical efficacy"
    ClaimBoundary.evidenceGraphClaim
    ClaimBoundary.clinicalClaim
    ClaimBoundary.clinicalEvidenceAuthorityBridgeReceipt
    ClaimBoundary.missingClinicalEvidenceReason
    "Human intervention requires valid consent, safety review, a sham, prespecified endpoint, registered analysis and independent replication."

mirrorEmpiricalPromotionStillBlocked :
  ClaimBoundary.targetClaimPromoted mirrorEmpiricalClaimBoundary ≡ false
mirrorEmpiricalPromotionStillBlocked =
  ClaimBoundary.targetClaimPromotedIsFalse mirrorEmpiricalClaimBoundary

mirrorClinicalPromotionStillBlocked :
  ClaimBoundary.targetClaimPromoted mirrorClinicalClaimBoundary ≡ false
mirrorClinicalPromotionStillBlocked =
  ClaimBoundary.targetClaimPromotedIsFalse mirrorClinicalClaimBoundary

-- PredictionProtocol remains the canonical quantitative/holdout contract.
-- This module intentionally does not construct a prediction value or proof of
-- empirical confirmation and does not reclassify any p-adic Kozyrev theorem.

------------------------------------------------------------------------
-- Repo-native torsion reconciliation (current source owners, not new physics).
--
-- Torque369: merged PR #1164, Levi-Civita orientation of ordered r/F axes.
-- SignedZero: path/arrival-direction bookkeeping (NOT GR connection torsion).
-- LeviCivita: torsion-free connection as a conditional supplied witness.
-- EinsteinCartanAudit: open theory/operator/decoupling identity bridges.
-- POAMS: ordinary angular-momentum law; preliminary claims remain separate.
--
-- This is a typed *disambiguation*, not a coupling of the named objects.
------------------------------------------------------------------------

data TorsionMeaning : Set where
  mechanicalTwistOrTorque : TorsionMeaning
  signedZeroPathTorsionSemantics : TorsionMeaning
  differentialGeometricConnectionTorsion : TorsionMeaning
  claimedKozyrevInformationTorsion : TorsionMeaning
  algebraicTwoTorsionUnrelated : TorsionMeaning

mechanicalTorsionIsNotClaimedInformationField :
  mechanicalTwistOrTorque ≢ claimedKozyrevInformationTorsion
mechanicalTorsionIsNotClaimedInformationField ()

geometricTorsionIsNotClaimedInformationField :
  differentialGeometricConnectionTorsion ≢ claimedKozyrevInformationTorsion
geometricTorsionIsNotClaimedInformationField ()

signedZeroTorsionIsNotGeometricTorsion :
  signedZeroPathTorsionSemantics ≢ differentialGeometricConnectionTorsion
signedZeroTorsionIsNotGeometricTorsion ()

ellipticTorsionIsNotMechanicalTorsion :
  algebraicTwoTorsionUnrelated ≢ mechanicalTwistOrTorque
ellipticTorsionIsNotMechanicalTorsion ()

-- This function reuses the *real* finite orientation carrier/proof owner.
-- It proves only swapping the lever/force labels twice preserves that voxel.
mirrorMechanicalOrientationRoundTrip :
  (voxel : Torque369.BracketVoxel) →
  Torque369.swapTorqueInputs (Torque369.swapTorqueInputs voxel) ≡ voxel
mirrorMechanicalOrientationRoundTrip =
  Torque369.swapTorqueInputsInvolutive

-- Both directed signed-zero labels have one canonical neutral scalar.
-- Reuse exactly the existing source theorem's definitional computation.
mirrorPlusMinusZeroSameScalar :
  SignedZero.signedZeroScalarValue SignedZero.plusZero
  ≡ SignedZero.signedZeroScalarValue SignedZero.minusZero
mirrorPlusMinusZeroSameScalar = refl

-- A conditional torsion-free metric-compatible connection cannot, by name,
-- serve as evidence of a *nonzero*, apparatus-generated geometric torsion.
mirrorConditionalConnectionTorsionFreeWasAssumed :
  LeviCivita.torsionFree LeviCivita.canonicalConditionalConnection ≡ true
mirrorConditionalConnectionTorsionFreeWasAssumed = refl

-- The source audit has a different object: Einstein-Cartan-YM versus pure YM.
-- Reuse its original same-theory non-identity proof without renaming it
-- as an empirical Kozyrev-mirror measurement.
mirrorEinsteinCartanPureYMNonIdentity :
  PaperAudit.sourceTheory EinsteinCartanAudit.monographAudit
  ≡ PaperAudit.pureFourDimensionalYangMills → ⊥
mirrorEinsteinCartanPureYMNonIdentity =
  EinsteinCartanAudit.monographTheoryIsNotDefinitionallyPureYM

-- The established angular-momentum comparison is imported from POAMS;
-- preliminary POAMS data do not validate the mirror or a new coupling.
mirrorAngularMomentumBaseline :
  Science.ScientificMechanismReceipt
mirrorAngularMomentumBaseline = POAMS.angularMomentumConservation

------------------------------------------------------------------------
-- Gated bridge request: none of these fields is filled by syntactic reuse.
-- A real bridge must couple a source, apparatus, calibrated observable,
-- dimensionful prediction, null model, and independently replicated data.
------------------------------------------------------------------------

data PhysicalTorsionBridgeRequirement : Set where
  specifyMetricAndConnectionSource : PhysicalTorsionBridgeRequirement
  deriveTorsionGeneratingSpinSource : PhysicalTorsionBridgeRequirement
  deriveApparatusCouplingToConnection : PhysicalTorsionBridgeRequirement
  specifySIUnitsAndInstrumentResponse : PhysicalTorsionBridgeRequirement
  deriveQuantitativeNonzeroPrediction : PhysicalTorsionBridgeRequirement
  establishOrdinaryEMAcousticMechanicalNull : PhysicalTorsionBridgeRequirement
  preregisterAndFreezeShamRandomization : PhysicalTorsionBridgeRequirement
  calibrateAndBoundUncertainty : PhysicalTorsionBridgeRequirement
  independentlyReplicateHeldOutSignal : PhysicalTorsionBridgeRequirement
  preserveScientificClaimAuthorityReview : PhysicalTorsionBridgeRequirement

canonicalTorsionBridgeRequirements :
  List PhysicalTorsionBridgeRequirement
canonicalTorsionBridgeRequirements =
  specifyMetricAndConnectionSource
  ∷ deriveTorsionGeneratingSpinSource
  ∷ deriveApparatusCouplingToConnection
  ∷ specifySIUnitsAndInstrumentResponse
  ∷ deriveQuantitativeNonzeroPrediction
  ∷ establishOrdinaryEMAcousticMechanicalNull
  ∷ preregisterAndFreezeShamRandomization
  ∷ calibrateAndBoundUncertainty
  ∷ independentlyReplicateHeldOutSignal
  ∷ preserveScientificClaimAuthorityReview
  ∷ []

record TorsionBridgeReadiness : Set where
  constructor torsionBridgeReadiness
  field
    orientationAndClaimFamiliesDisambiguated : Bool
    orientationAndClaimFamiliesDisambiguatedIsTrue :
      orientationAndClaimFamiliesDisambiguated ≡ true
    geometricConnectionSourceDerivedFromMirror : Bool
    geometricConnectionSourceDerivedFromMirrorIsFalse :
      geometricConnectionSourceDerivedFromMirror ≡ false
    quantitativePhysicalCouplingDerived : Bool
    quantitativePhysicalCouplingDerivedIsFalse :
      quantitativePhysicalCouplingDerived ≡ false
    torsionInstrumentCalibrated : Bool
    torsionInstrumentCalibratedIsFalse :
      torsionInstrumentCalibrated ≡ false
    torsionSignalReplicated : Bool
    torsionSignalReplicatedIsFalse :
      torsionSignalReplicated ≡ false
    torsionFieldPhysicallyPromoted : Bool
    torsionFieldPhysicallyPromotedIsFalse :
      torsionFieldPhysicallyPromoted ≡ false

canonicalTorsionBridgeReadiness : TorsionBridgeReadiness
canonicalTorsionBridgeReadiness =
  torsionBridgeReadiness
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

-- No empty-space torsion assumption or claimed information-transfer effect
-- is smuggled in by importing finite kinematics or signed-zero labels.

------------------------------------------------------------------------
-- Discovery cut: inherited spiral/wreath/helix/mirror-owner exact results.
--
-- No new spiral parameterisation, wreath multiplication or reflection
-- calculus is constructed in the Kozyrev case owner.
------------------------------------------------------------------------

mirrorExistingFiniteWreathRoundTrip :
  (assignment : ExistingFiniteWreath.Assignment) →
  (site : ExistingFiniteWreath.TwoSite) →
  ExistingFiniteWreath.localPermutationStep
    (ExistingFiniteWreath.localPermutationStep assignment) site
  ≡ assignment site
mirrorExistingFiniteWreathRoundTrip =
  ExistingFiniteWreath.localPermutationStepTwiceAt

mirrorExistingRecursiveWreathInverse :
  ExistingWreath.act
    (ExistingWreath.inverseAut ExistingWreath.canonicalDepthTwoAut)
    (ExistingWreath.act
      ExistingWreath.canonicalDepthTwoAut ExistingWreath.samplePath)
  ≡ ExistingWreath.samplePath
mirrorExistingRecursiveWreathInverse =
  ExistingWreath.sampleInverseRoundTrip

mirrorExistingHelicalPhaseReturn :
  (site : ExistingHelix.HelicalSite) →
  ExistingHelix.stitchPhase (ExistingHelix.helicalThreeSteps site)
  ≡ ExistingHelix.stitchPhase site
mirrorExistingHelicalPhaseReturn =
  ExistingHelix.threeStepsReturnToSamePhase

mirrorExistingSpiralSenseParity :
  (state : ExistingSpiral.SpiralState) →
  ExistingSpiral.spiralSense (ExistingSpiral.liftReflection state)
  ≡ ExistingSpiral.flipSense (ExistingSpiral.spiralSense state)
mirrorExistingSpiralSenseParity =
  ExistingSpiral.reflectionFlipsSpiralSense

mirrorExistingWindingProjectionNoninjectiveWitness :
  ExistingWinding.nineToSixForgetsWinding ExistingWinding.sampleHelixZero
  ≡ ExistingWinding.nineToSixForgetsWinding ExistingWinding.sampleHelixOne
mirrorExistingWindingProjectionNoninjectiveWitness =
  ExistingWinding.sameCircularProjectionDifferentHistory

mirrorExistingStationaryPhaseMirrorSetup :
  ExistingOptics.StationaryPhaseToySetup
mirrorExistingStationaryPhaseMirrorSetup =
  ExistingOptics.mirrorFermatToySetup

mirrorExistingPerfectConductorBoundaryKind :
  ExistingMaxwell.BoundaryConditionClass
mirrorExistingPerfectConductorBoundaryKind =
  ExistingMaxwell.tangentialElectricZero

------------------------------------------------------------------------
-- These exact imported theorems prove their own source-native semantics.
-- No source-native theorem states that a metal enclosure implements a
-- particular wreath automorphism, log-polar spiral, Maxwell spectrum or
-- physical spacetime-torsion source. An explicit, calibrated realisation
-- and boundary-value problem must supply those identifications.
------------------------------------------------------------------------

data ExistingGeometryKozyrevRealisationRequirement : Set where
  selectPatentEditionAndMeasuredSurface : ExistingGeometryKozyrevRealisationRequirement
  supplySurfaceCoordinateMapIntoExistingGeometry : ExistingGeometryKozyrevRealisationRequirement
  proveHandednessAndBoundaryTransport : ExistingGeometryKozyrevRealisationRequirement
  identifyPhysicalMaterialConstitutiveParameters : ExistingGeometryKozyrevRealisationRequirement
  identifyMaxwellOrAcousticOperatorOnSameGeometry : ExistingGeometryKozyrevRealisationRequirement
  supplyInstrumentResponseAndUncertainty : ExistingGeometryKozyrevRealisationRequirement
  compareHeldOutShamAndActiveOnSameObservable : ExistingGeometryKozyrevRealisationRequirement

canonicalExistingGeometryRealisationCut :
  List ExistingGeometryKozyrevRealisationRequirement
canonicalExistingGeometryRealisationCut =
  selectPatentEditionAndMeasuredSurface
  ∷ supplySurfaceCoordinateMapIntoExistingGeometry
  ∷ proveHandednessAndBoundaryTransport
  ∷ identifyPhysicalMaterialConstitutiveParameters
  ∷ identifyMaxwellOrAcousticOperatorOnSameGeometry
  ∷ supplyInstrumentResponseAndUncertainty
  ∷ compareHeldOutShamAndActiveOnSameObservable
  ∷ []

record ExistingGeometryReuseBoundary : Set where
  constructor existingGeometryReuseBoundary
  field
    spiralAndWreathMathematicsAvailable : Bool
    spiralAndWreathMathematicsAvailableIsTrue :
      spiralAndWreathMathematicsAvailable ≡ true
    measuredMirrorSurfaceSelected : Bool
    measuredMirrorSurfaceSelectedIsFalse :
      measuredMirrorSurfaceSelected ≡ false
    exactMaterialBoundaryOperatorRealised : Bool
    exactMaterialBoundaryOperatorRealisedIsFalse :
      exactMaterialBoundaryOperatorRealised ≡ false
    physicalTorsionPredictionDerived : Bool
    physicalTorsionPredictionDerivedIsFalse :
      physicalTorsionPredictionDerived ≡ false

canonicalExistingGeometryReuseBoundary : ExistingGeometryReuseBoundary
canonicalExistingGeometryReuseBoundary =
  existingGeometryReuseBoundary true refl false refl false refl false refl
