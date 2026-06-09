module DASHI.Promotion.QuantumQFTObligations where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Constants.Registry as Registry

------------------------------------------------------------------------
-- Quantum/QFT promotion obligation index.
--
-- This module is a work queue with typed guards.  It records the evidence
-- needed before Schrodinger dynamics, Born semantics, or QFT can be promoted.
-- It intentionally does not promote those claims; every canonical row remains
-- blocked until an owner module supplies the required proof/authority token.

data QuantumPromotionTarget : Set where
  schrodingerDynamicsTarget : QuantumPromotionTarget
  bornSemanticsTarget : QuantumPromotionTarget
  qftPromotionTarget : QuantumPromotionTarget

data QuantumObligationFamily : Set where
  hilbertRepresentationFamily : QuantumObligationFamily
  selfAdjointHamiltonianFamily : QuantumObligationFamily
  stoneUnitaryEvolutionFamily : QuantumObligationFamily
  exponentialConstructionFamily : QuantumObligationFamily
  observableCalibrationFamily : QuantumObligationFamily
  outcomeSigmaAlgebraFamily : QuantumObligationFamily
  projectionProbabilityFamily : QuantumObligationFamily
  povmProbabilityFamily : QuantumObligationFamily
  statisticalSemanticsFamily : QuantumObligationFamily
  gnsVacuumFamily : QuantumObligationFamily
  localNetFamily : QuantumObligationFamily
  localityCovarianceSpectrumFamily : QuantumObligationFamily
  dhrDrReconstructionFamily : QuantumObligationFamily
  interactingRenormalizationFamily : QuantumObligationFamily

data EvidenceKind : Set where
  carrierEvidence : EvidenceKind
  domainEvidence : EvidenceKind
  theoremEvidence : EvidenceKind
  constructionEvidence : EvidenceKind
  adapterEvidence : EvidenceKind
  authorityEvidence : EvidenceKind
  empiricalEvidence : EvidenceKind
  blockerDischargeEvidence : EvidenceKind

data PromotionGuard : Set where
  quantumDynamicsPromotedGuard : PromotionGuard
  bornRulePromotedGuard : PromotionGuard
  qftPromotedGuard : PromotionGuard
  quantumEmpiricalAdequacyGuard : PromotionGuard

data ObligationState : Set where
  notStarted : ObligationState
  carrierNamed : ObligationState
  typedSurfacePresent : ObligationState
  adapterRequired : ObligationState
  proofRequired : ObligationState
  authorityRequired : ObligationState
  empiricalValidationRequired : ObligationState
  blockedNoPromotion : ObligationState

record EvidenceRequirement : Set₁ where
  field
    evidenceLabel : String
    evidenceKind : EvidenceKind
    ownerSurface : String
    requiredToken : String
    boundaryNotes : List String

open EvidenceRequirement public

record QuantumQFTObligationRow : Set₁ where
  field
    rowLabel : String
    target : QuantumPromotionTarget
    family : QuantumObligationFamily
    currentOwner : String
    currentReceipt : String
    consumingRegistryReceipt :
      Registry.QuantumKnownInputsReferenceReceipt
    requiredEvidence : List EvidenceRequirement
    openBlockers : List String
    guardToFlip : PromotionGuard
    currentState : ObligationState
    promoted : Bool
    promotedIsFalse : promoted ≡ false
    validationTarget : String
    claimSurface : String

open QuantumQFTObligationRow public

record QuantumQFTPromotionObligationReceipt : Set₁ where
  field
    receiptLabel : String
    sourcePopulationReceipt :
      Registry.KnownInputsPopulationReceipt
    sourceQuantumReceipt :
      Registry.QuantumKnownInputsReferenceReceipt
    schrodingerRows : List QuantumQFTObligationRow
    bornRows : List QuantumQFTObligationRow
    qftRows : List QuantumQFTObligationRow
    schrodingerRowCount : Nat
    bornRowCount : Nat
    qftRowCount : Nat
    totalRowCount : Nat
    quantumDynamicsPromoted : Bool
    quantumDynamicsPromotedIsFalse :
      quantumDynamicsPromoted ≡ false
    bornRulePromoted : Bool
    bornRulePromotedIsFalse :
      bornRulePromoted ≡ false
    qftPromoted : Bool
    qftPromotedIsFalse :
      qftPromoted ≡ false
    quantumEmpiricalAdequacyAccepted : Bool
    quantumEmpiricalAdequacyAcceptedIsFalse :
      quantumEmpiricalAdequacyAccepted ≡ false
    promotionBoundaryNotes : List String

open QuantumQFTPromotionObligationReceipt public

mkEvidence :
  String →
  EvidenceKind →
  String →
  String →
  List String →
  EvidenceRequirement
mkEvidence label kind owner token notes =
  record
    { evidenceLabel = label
    ; evidenceKind = kind
    ; ownerSurface = owner
    ; requiredToken = token
    ; boundaryNotes = notes
    }

mkRow :
  String →
  QuantumPromotionTarget →
  QuantumObligationFamily →
  String →
  String →
  List EvidenceRequirement →
  List String →
  PromotionGuard →
  ObligationState →
  String →
  String →
  QuantumQFTObligationRow
mkRow label target family owner receipt evidence blockers guard state
      validation claim =
  record
    { rowLabel = label
    ; target = target
    ; family = family
    ; currentOwner = owner
    ; currentReceipt = receipt
    ; consumingRegistryReceipt =
        Registry.canonicalQuantumKnownInputsReferenceReceipt
    ; requiredEvidence = evidence
    ; openBlockers = blockers
    ; guardToFlip = guard
    ; currentState = state
    ; promoted = false
    ; promotedIsFalse = refl
    ; validationTarget = validation
    ; claimSurface = claim
    }

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Shared evidence clauses.

hilbertRepresentationEvidence : List EvidenceRequirement
hilbertRepresentationEvidence =
  mkEvidence
    "physical Hilbert carrier"
    carrierEvidence
    "DASHI.Physics.Closure.SchrodingerEvolutionScope"
    "PhysicalHilbertRepresentationToken"
    ( "must identify the complex Hilbert space, inner product, completion, and physical state carrier"
    ∷ "finite phase-wave packaging is not enough"
    ∷ []
    )
  ∷ mkEvidence
    "registry constant binding"
    adapterEvidence
    "DASHI.Constants.Registry"
    "QuantumConstantsUnitBindingToken"
    ( "must bind hbar, h, c, e, and mass inputs to the represented Hamiltonian units"
    ∷ []
    )
  ∷ []

selfAdjointHamiltonianEvidence : List EvidenceRequirement
selfAdjointHamiltonianEvidence =
  mkEvidence
    "dense Hamiltonian domain"
    domainEvidence
    "DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt"
    "DenseHamiltonianDomainToken"
    ( "must name the operator domain and prove density"
    ∷ []
    )
  ∷ mkEvidence
    "self-adjointness theorem"
    theoremEvidence
    "DASHI.Quantum.SelfAdjointGenerator"
    "SelfAdjointHamiltonianToken"
    ( "Kato-Rellich, essential self-adjointness, or an explicitly scoped substitute must be supplied"
    ∷ []
    )
  ∷ []

stoneUnitaryEvidence : List EvidenceRequirement
stoneUnitaryEvidence =
  mkEvidence
    "Stone theorem bridge"
    theoremEvidence
    "DASHI.Quantum.Stone"
    "StoneStronglyContinuousUnitaryGroupToken"
    ( "must connect the self-adjoint generator to a strongly continuous one-parameter unitary group"
    ∷ []
    )
  ∷ mkEvidence
    "unitary evolution preservation"
    theoremEvidence
    "DASHI.Algebra.Quantum.Unitary"
    "SchrodingerUnitaryEvolutionToken"
    ( "basis-level finite norm preservation is not a physical time-evolution theorem"
    ∷ []
    )
  ∷ []

exponentialConstructionEvidence : List EvidenceRequirement
exponentialConstructionEvidence =
  mkEvidence
    "Hamiltonian exponential"
    constructionEvidence
    "DASHI.Physics.Closure.SchrodingerEvolutionScope"
    "ExpMinusITHOverHbarConstructionToken"
    ( "must construct exp(-i t H / hbar) in the represented Hilbert space"
    ∷ []
    )
  ∷ mkEvidence
    "Schrodinger equation differentiation"
    theoremEvidence
    "DASHI.Physics.SchrodingerAssumedTheorem"
    "SchrodingerDifferentiationToken"
    ( "must prove that the constructed evolution satisfies the target differential equation"
    ∷ []
    )
  ∷ []

outcomeSigmaEvidence : List EvidenceRequirement
outcomeSigmaEvidence =
  mkEvidence
    "outcome measurable space"
    carrierEvidence
    "DASHI.Physics.Measurement"
    "OutcomeSigmaAlgebraToken"
    ( "must supply outcomes, events, and sigma-algebra closure laws"
    ∷ []
    )
  ∷ mkEvidence
    "observable-to-event adapter"
    adapterEvidence
    "DASHI.Physics.Closure.HEPDataMeasurementSurfaceProjectionRejection"
    "ObservableEventProjectionToken"
    ( "must show how repo observables land in measurable events"
    ∷ []
    )
  ∷ []

projectionProbabilityEvidence : List EvidenceRequirement
projectionProbabilityEvidence =
  mkEvidence
    "projection-valued measurement"
    theoremEvidence
    "DASHI.Algebra.Quantum.Measurement"
    "ProjectionProbabilityMeasureToken"
    ( "must prove positivity, normalization, and countable additivity for the projection semantics"
    ∷ []
    )
  ∷ mkEvidence
    "state normalization"
    theoremEvidence
    "DASHI.Physics.Measurement"
    "NormalisedQuantumStateToken"
    ( "must prevent probability interpretation for unnormalised carriers"
    ∷ []
    )
  ∷ []

povmProbabilityEvidence : List EvidenceRequirement
povmProbabilityEvidence =
  mkEvidence
    "POVM measurement semantics"
    theoremEvidence
    "DASHI.Physics.Measurement"
    "POVMProbabilityMeasureToken"
    ( "must supply positive operator valued effects and probability-measure laws"
    ∷ []
    )
  ∷ mkEvidence
    "Born-like adapter equivalence"
    adapterEvidence
    "DASHI.Physics.Measurement"
    "BornLikeAdapterEquivalenceToken"
    ( "must identify when projection semantics and POVM semantics agree"
    ∷ []
    )
  ∷ []

statisticalSemanticsEvidence : List EvidenceRequirement
statisticalSemanticsEvidence =
  mkEvidence
    "repeat-trial statistical semantics"
    empiricalEvidence
    "DASHI.Physics.Prediction"
    "RepeatedMeasurementCalibrationToken"
    ( "must connect probabilities to repeated measurements, uncertainty, and empirical comparison"
    ∷ []
    )
  ∷ mkEvidence
    "measurement surface comparison"
    adapterEvidence
    "DASHI.Constants.Registry"
    "QuantumMeasurementProviderComparisonToken"
    ( "must consume provider/covariance/comparison-law receipts before empirical adequacy can move"
    ∷ []
    )
  ∷ []

gnsVacuumEvidence : List EvidenceRequirement
gnsVacuumEvidence =
  mkEvidence
    "C-star algebra and state"
    carrierEvidence
    "DASHI.Physics.QFT.GNSFellRepresentationSurface"
    "CStarAlgebraStateToken"
    ( "must name the algebra and positive normalized state"
    ∷ []
    )
  ∷ mkEvidence
    "GNS Hilbert representation"
    constructionEvidence
    "DASHI.Quantum.GNSUniversalProperty"
    "GNSRepresentationToken"
    ( "must construct the representation, cyclic vector, and universal property"
    ∷ []
    )
  ∷ mkEvidence
    "vacuum state"
    authorityEvidence
    "DASHI.Physics.QFT.ModularTheoryReceiptSurface"
    "VacuumStateSelectionToken"
    ( "must distinguish vacuum selection from a generic algebraic state"
    ∷ []
    )
  ∷ []

localNetEvidence : List EvidenceRequirement
localNetEvidence =
  mkEvidence
    "concrete region carrier"
    carrierEvidence
    "DASHI.Physics.QFT.AQFTTypedNetSurface"
    "ConcreteRegionCarrierToken"
    ( "the current AQFT surface postulates regions; promotion requires a concrete carrier"
    ∷ []
    )
  ∷ mkEvidence
    "local algebra net"
    constructionEvidence
    "DASHI.Physics.QFT.AQFTTypedNetSurface"
    "HaagKastlerLocalNetToken"
    ( "must supply local algebras, inclusions, morphisms, and isotony"
    ∷ []
    )
  ∷ []

localityCovarianceSpectrumEvidence : List EvidenceRequirement
localityCovarianceSpectrumEvidence =
  mkEvidence
    "locality and causal separation"
    theoremEvidence
    "DASHI.Physics.QFT.AQFTTypedNetSurface"
    "EinsteinLocalityToken"
    ( "must prove commutation/independence for causally separated regions"
    ∷ []
    )
  ∷ mkEvidence
    "covariance representation"
    theoremEvidence
    "DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface"
    "PoincareCovarianceToken"
    ( "must provide the spacetime symmetry action and covariance law"
    ∷ []
    )
  ∷ mkEvidence
    "spectrum condition"
    theoremEvidence
    "DASHI.Physics.QFT.StressEnergyBridgeReceiptSurface"
    "PositiveEnergySpectrumToken"
    ( "must prove the physical spectrum condition in the chosen representation"
    ∷ []
    )
  ∷ []

dhrDrEvidence : List EvidenceRequirement
dhrDrEvidence =
  mkEvidence
    "DHR selection criterion"
    theoremEvidence
    "DASHI.Physics.QFT.DHRGaugeReceiptSurface"
    "DHRSelectionCriterionToken"
    ( "must promote localised transportable endomorphisms beyond finite ledger rows"
    ∷ []
    )
  ∷ mkEvidence
    "DR reconstruction authority"
    authorityEvidence
    "DASHI.Physics.QFT.DHRTensorDualGroupReconstruction"
    "DoplicherRobertsReconstructionToken"
    ( "must reconstruct the compact gauge group under the required hypotheses"
    ∷ []
    )
  ∷ mkEvidence
    "SM carrier-functor match"
    blockerDischargeEvidence
    "DASHI.Physics.QFT.ExactSMMatchToken"
    "ExactSMCarrierFunctorMatchToken"
    ( "finite p2/p3/p5 compatibility does not imply full Standard Model equality"
    ∷ []
    )
  ∷ []

interactingRenormalizationEvidence : List EvidenceRequirement
interactingRenormalizationEvidence =
  mkEvidence
    "interacting construction"
    theoremEvidence
    "DASHI.Physics.Closure.InteractingQFTBoundaryReceipt"
    "InteractingQFTConstructionToken"
    ( "must specify the model, interaction, regulator, and nontrivial continuum object"
    ∷ []
    )
  ∷ mkEvidence
    "renormalization and continuum limit"
    theoremEvidence
    "DASHI.Physics.Closure.YMConstructiveQFTFlagRouteReceipt"
    "RenormalizedContinuumLimitToken"
    ( "must discharge regulator independence or the explicitly scoped constructive route"
    ∷ []
    )
  ∷ mkEvidence
    "empirical or Clay-facing adequacy boundary"
    empiricalEvidence
    "DASHI.Constants.Registry"
    "QFTEmpiricalAdequacyOrClayAuthorityToken"
    ( "must be an external authority/proof token; registry source population is insufficient"
    ∷ []
    )
  ∷ []

------------------------------------------------------------------------
-- Canonical rows.

canonicalSchrodingerObligationRows : List QuantumQFTObligationRow
canonicalSchrodingerObligationRows =
  mkRow
    "Schrodinger Hilbert representation"
    schrodingerDynamicsTarget
    hilbertRepresentationFamily
    "DASHI.Physics.Closure.SchrodingerEvolutionScope"
    "canonicalG3SchrodingerInputs / canonicalSchrodingerEvolutionScope"
    hilbertRepresentationEvidence
    ( "missing physical Hilbert space representation"
    ∷ "missing unit/constant binding into Hamiltonian scale"
    ∷ []
    )
    quantumDynamicsPromotedGuard
    typedSurfacePresent
    "agda -i . DASHI/Physics/Closure/SchrodingerEvolutionScope.agda"
    "Docs/SchrodingerEvolutionScope.md"
  ∷ mkRow
    "Schrodinger self-adjoint Hamiltonian"
    schrodingerDynamicsTarget
    selfAdjointHamiltonianFamily
    "DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt"
    "Schrodinger self-adjoint evolution receipt"
    selfAdjointHamiltonianEvidence
    ( "missing dense domain"
    ∷ "missing self-adjointness proof"
    ∷ "missing Kato-Rellich or scoped substitute"
    ∷ []
    )
    quantumDynamicsPromotedGuard
    proofRequired
    "agda -i . DASHI/Physics/Closure/SchrodingerSelfAdjointEvolutionReceipt.agda"
    "Docs/SchrodingerEvolutionScope.md"
  ∷ mkRow
    "Stone/unitary Schrodinger evolution"
    schrodingerDynamicsTarget
    stoneUnitaryEvolutionFamily
    "DASHI.Quantum.Stone"
    "Stone theorem and unitary evolution bridge"
    stoneUnitaryEvidence
    ( "missing strongly continuous one-parameter unitary group"
    ∷ "missing physical norm-preservation theorem"
    ∷ []
    )
    quantumDynamicsPromotedGuard
    proofRequired
    "agda -i . DASHI/Quantum/Stone.agda"
    "Docs/SchrodingerEvolutionScope.md"
  ∷ mkRow
    "Schrodinger exponential construction"
    schrodingerDynamicsTarget
    exponentialConstructionFamily
    "DASHI.Physics.SchrodingerAssumedTheorem"
    "assumedTheoremFromGap boundary"
    exponentialConstructionEvidence
    ( "missing exp(-i t H / hbar) construction"
    ∷ "missing differential-equation satisfaction proof"
    ∷ []
    )
    quantumDynamicsPromotedGuard
    proofRequired
    "agda -i . DASHI/Physics/SchrodingerAssumedTheorem.agda"
    "Docs/SchrodingerEvolutionScope.md"
  ∷ mkRow
    "Schrodinger observable calibration"
    schrodingerDynamicsTarget
    observableCalibrationFamily
    "DASHI.Constants.Registry"
    "canonicalQuantumKnownInputsReferenceReceipt"
    ( mkEvidence
        "observable and unit calibration"
        adapterEvidence
        "DASHI.Constants.Registry"
        "SchrodingerObservableCalibrationToken"
        ( "must bind hbar and measured masses to observables without deriving them from carriers"
        ∷ []
        )
    ∷ []
    )
    ( "missing physical observable map"
    ∷ "missing calibration authority consumption"
    ∷ []
    )
    quantumDynamicsPromotedGuard
    adapterRequired
    "agda -i . DASHI/Constants/Registry.agda"
    "Docs/UnifiedRoutesLanePlan.md"
  ∷ []

canonicalBornObligationRows : List QuantumQFTObligationRow
canonicalBornObligationRows =
  mkRow
    "Born outcome sigma algebra"
    bornSemanticsTarget
    outcomeSigmaAlgebraFamily
    "DASHI.Physics.Measurement"
    "PredictionTheory / MeasurementTheory / QuantumMeasurement"
    outcomeSigmaEvidence
    ( "missing outcome sigma algebra"
    ∷ "missing observable-to-event projection"
    ∷ []
    )
    bornRulePromotedGuard
    carrierNamed
    "agda -i . DASHI/Physics/Measurement.agda"
    "Docs/MeasurementSurfaceProjectionContract.md"
  ∷ mkRow
    "Born projection probability semantics"
    bornSemanticsTarget
    projectionProbabilityFamily
    "DASHI.Algebra.Quantum.Measurement"
    "measurement-not-invertible boundary"
    projectionProbabilityEvidence
    ( "projection/non-invertibility is not a probability measure"
    ∷ "missing state normalization"
    ∷ []
    )
    bornRulePromotedGuard
    proofRequired
    "agda -i . DASHI/Algebra/Quantum/Measurement.agda"
    "Docs/MeasurementSurfaceProjectionContract.md"
  ∷ mkRow
    "Born POVM probability semantics"
    bornSemanticsTarget
    povmProbabilityFamily
    "DASHI.Physics.Measurement"
    "BornLike / QuantumMeasurement"
    povmProbabilityEvidence
    ( "missing positive operator valued measure laws"
    ∷ "missing equivalence/scope against projection-valued semantics"
    ∷ []
    )
    bornRulePromotedGuard
    proofRequired
    "agda -i . DASHI/Physics/Measurement.agda"
    "Docs/MeasurementSurfaceProjectionContract.md"
  ∷ mkRow
    "Born statistical and empirical semantics"
    bornSemanticsTarget
    statisticalSemanticsFamily
    "DASHI.Physics.Prediction"
    "prediction/measurement comparison boundary"
    statisticalSemanticsEvidence
    ( "missing repeated-measurement semantics"
    ∷ "missing provider comparison and covariance receipts"
    ∷ "missing empirical adequacy token"
    ∷ []
    )
    quantumEmpiricalAdequacyGuard
    empiricalValidationRequired
    "agda -i . DASHI/Physics/Prediction.agda"
    "Docs/UnifiedRoutesLanePlan.md"
  ∷ []

canonicalQFTObligationRows : List QuantumQFTObligationRow
canonicalQFTObligationRows =
  mkRow
    "QFT GNS vacuum representation"
    qftPromotionTarget
    gnsVacuumFamily
    "DASHI.Physics.QFT.GNSFellRepresentationSurface"
    "GNS/Fell representation surface"
    gnsVacuumEvidence
    ( "missing concrete C-star algebra/state"
    ∷ "missing GNS representation construction"
    ∷ "missing vacuum selection"
    ∷ []
    )
    qftPromotedGuard
    adapterRequired
    "agda -i . DASHI/Physics/QFT/GNSFellRepresentationSurface.agda"
    "Docs/UnifiedRoutesLanePlan.md"
  ∷ mkRow
    "AQFT local net construction"
    qftPromotionTarget
    localNetFamily
    "DASHI.Physics.QFT.AQFTTypedNetSurface"
    "canonicalAQFTTypedNetSurface"
    localNetEvidence
    ( "current regions/local algebras are sockets"
    ∷ "missing concrete Haag-Kastler net"
    ∷ []
    )
    qftPromotedGuard
    typedSurfacePresent
    "agda -i . DASHI/Physics/QFT/AQFTTypedNetSurface.agda"
    "Docs/UnifiedRoutesLanePlan.md"
  ∷ mkRow
    "AQFT locality covariance spectrum"
    qftPromotionTarget
    localityCovarianceSpectrumFamily
    "DASHI.Physics.QFT.AQFTTypedNetSurface"
    "AQFT typed net law boundary"
    localityCovarianceSpectrumEvidence
    ( "missing locality law from concrete net"
    ∷ "missing covariance representation"
    ∷ "missing positive-energy spectrum condition"
    ∷ []
    )
    qftPromotedGuard
    proofRequired
    "agda -i . DASHI/Physics/QFT/AQFTTypedNetSurface.agda"
    "Docs/UnifiedRoutesLanePlan.md"
  ∷ mkRow
    "DHR/DR gauge reconstruction"
    qftPromotionTarget
    dhrDrReconstructionFamily
    "DASHI.Physics.QFT.DHRGaugeReceiptSurface"
    "DHR gauge receipt / DR reconstruction boundary"
    dhrDrEvidence
    ( "finite lane rows do not supply arbitrary DHR sector closure"
    ∷ "missing DR reconstruction under full hypotheses"
    ∷ "missing exact SM carrier-functor match"
    ∷ []
    )
    qftPromotedGuard
    authorityRequired
    "agda -i . DASHI/Physics/QFT/DHRGaugeReceiptSurface.agda"
    "Docs/UnifiedRoutesLanePlan.md"
  ∷ mkRow
    "Interacting QFT and renormalization"
    qftPromotionTarget
    interactingRenormalizationFamily
    "DASHI.Physics.Closure.InteractingQFTBoundaryReceipt"
    "interacting QFT boundary receipt"
    interactingRenormalizationEvidence
    ( "missing interacting continuum construction"
    ∷ "missing renormalization or constructive transfer theorem"
    ∷ "missing empirical/Clay authority token"
    ∷ []
    )
    qftPromotedGuard
    blockedNoPromotion
    "agda -i . DASHI/Physics/Closure/InteractingQFTBoundaryReceipt.agda"
    "Docs/UnifiedRoutesLanePlan.md"
  ∷ []

canonicalQuantumQFTPromotionObligationReceipt :
  QuantumQFTPromotionObligationReceipt
canonicalQuantumQFTPromotionObligationReceipt = record
  { receiptLabel = "canonical quantum/QFT promotion obligations"
  ; sourcePopulationReceipt =
      Registry.canonicalKnownInputsPopulationReceipt
  ; sourceQuantumReceipt =
      Registry.canonicalQuantumKnownInputsReferenceReceipt
  ; schrodingerRows = canonicalSchrodingerObligationRows
  ; bornRows = canonicalBornObligationRows
  ; qftRows = canonicalQFTObligationRows
  ; schrodingerRowCount =
      listCount canonicalSchrodingerObligationRows
  ; bornRowCount =
      listCount canonicalBornObligationRows
  ; qftRowCount =
      listCount canonicalQFTObligationRows
  ; totalRowCount =
      listCount canonicalSchrodingerObligationRows
      + listCount canonicalBornObligationRows
      + listCount canonicalQFTObligationRows
  ; quantumDynamicsPromoted = false
  ; quantumDynamicsPromotedIsFalse = refl
  ; bornRulePromoted = false
  ; bornRulePromotedIsFalse = refl
  ; qftPromoted = false
  ; qftPromotedIsFalse = refl
  ; quantumEmpiricalAdequacyAccepted = false
  ; quantumEmpiricalAdequacyAcceptedIsFalse = refl
  ; promotionBoundaryNotes =
      "Schrodinger rows require Hilbert, self-adjoint, Stone, exponential, and calibration evidence before promotion"
      ∷ "Born rows require measurable outcome semantics, probability-measure laws, and statistical/empirical adapters before promotion"
      ∷ "QFT rows require concrete GNS/vacuum/local-net, locality/covariance/spectrum, DHR/DR, and interacting/renormalization evidence before promotion"
      ∷ "exact constants and populated quantum law slots are consumed as external inputs, not as derivations"
      ∷ []
  }

canonicalSchrodingerObligationCountIs5 :
  QuantumQFTPromotionObligationReceipt.schrodingerRowCount
    canonicalQuantumQFTPromotionObligationReceipt
  ≡ 5
canonicalSchrodingerObligationCountIs5 = refl

canonicalBornObligationCountIs4 :
  QuantumQFTPromotionObligationReceipt.bornRowCount
    canonicalQuantumQFTPromotionObligationReceipt
  ≡ 4
canonicalBornObligationCountIs4 = refl

canonicalQFTObligationCountIs5 :
  QuantumQFTPromotionObligationReceipt.qftRowCount
    canonicalQuantumQFTPromotionObligationReceipt
  ≡ 5
canonicalQFTObligationCountIs5 = refl

canonicalQuantumQFTObligationCountIs14 :
  QuantumQFTPromotionObligationReceipt.totalRowCount
    canonicalQuantumQFTPromotionObligationReceipt
  ≡ 14
canonicalQuantumQFTObligationCountIs14 = refl
