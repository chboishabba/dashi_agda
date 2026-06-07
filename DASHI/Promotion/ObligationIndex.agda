module DASHI.Promotion.ObligationIndex where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Interop.CategoricalInterlinkLayer as Interlink
import DASHI.Promotion.NumericAndAuthorityObligations as Numeric
import DASHI.Promotion.ClassicalFieldObligations as Classical
import DASHI.Promotion.QuantumQFTObligations as Quantum
import DASHI.Promotion.ChemistryBiologyObligations as ChemBio
import DASHI.Promotion.Gate3ClayObligations as GateClay
import DASHI.Promotion.StandardModelTerminalObligations as SMT
import DASHI.Promotion.NumericMeasuredAuthorityBinding as Measured
import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Maxwell
import DASHI.Promotion.FiniteQuantumSchrodingerBornAdapter as FiniteQuantum
import DASHI.Promotion.ChemistryQuantitativeAdapter as ChemistryAdapter
import DASHI.Promotion.EmpiricalRuntimeReplayAdapter as RuntimeAdapter
import DASHI.Promotion.Gate3StandardModelClayEvidenceReducer as Reducer
import DASHI.Promotion.NumericAuthorityTokenIntake as NumericIntake
import DASHI.Promotion.MaxwellHodgeSourceCalibration as MaxwellCalibration
import DASHI.Promotion.QuantumFiniteToGeneralBoundary as QuantumBoundary
import DASHI.Promotion.ChemistrySpectroscopyAuthorityIntake as ChemAuthority
import DASHI.Promotion.EmpiricalReplayAcceptanceCriteria as ReplayCriteria
import DASHI.Promotion.ClayProofTranslationReducer as ClayTranslation
import DASHI.Promotion.FiniteQuantumPhysicalScopeDecision as QuantumScope
import DASHI.Promotion.GRBoundaryClarification as GRScope
import DASHI.Promotion.BiologyFiniteScopeClarification as BiologyScope
import DASHI.Promotion.ChemistryFiniteRuleTargets as ChemistryRules
import DASHI.Physics.Closure.YMCompletionBoundaryTightening as YMScope
import DASHI.Physics.Closure.NSMigrationInitiationThresholdConstantsReceipt as NSConstants
import DASHI.Physics.Closure.YMExternalAcceptancePacketNormalization as YMExternal
import DASHI.Promotion.StandardModelFiniteRepresentationNarrowing as SMNarrowing
import DASHI.Promotion.MaxwellHodgeSourceConservationObligations as MaxwellConservation
import DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization as NumericNormalization
import DASHI.Promotion.ChemistryAuthorityBinding as ChemistryBinding
import DASHI.Physics.Closure.NSSprint150SourceViscosityBalanceReceipt as NS150
import DASHI.Promotion.ChemistryFiniteComputationSurface as ChemistryComputation
import DASHI.Promotion.StandardModelFiniteAnomalyHyperchargeCheck as SMAnomaly
import DASHI.Promotion.MaxwellFiniteExteriorChainStrengthening as MaxwellChain
import DASHI.Promotion.NumericAuthorityPayloadValidator as NumericPayload
import DASHI.Promotion.FiniteQuantumQFTScopedClosure as QuantumClosure

------------------------------------------------------------------------
-- Unified promotion obligation index.
--
-- This is the sprint-facing queue for promotion work.  It joins the six
-- disjoint implementation lanes into one receipt surface and deliberately
-- keeps the promoted-claim bit false.  Rows here are obligations to satisfy,
-- not theorem claims.

data PromotionImplementationLane : Set where
  numericAndAuthorityLane : PromotionImplementationLane
  classicalFieldLane : PromotionImplementationLane
  quantumQFTLane : PromotionImplementationLane
  chemistryBiologyLane : PromotionImplementationLane
  gate3ClayLane : PromotionImplementationLane
  standardModelTerminalLane : PromotionImplementationLane

data AdapterAdvancementLane : Set where
  measuredAuthorityAdapterLane : AdapterAdvancementLane
  maxwellExteriorCalculusLane : AdapterAdvancementLane
  finiteQuantumBornLane : AdapterAdvancementLane
  chemistryQuantitativeLane : AdapterAdvancementLane
  empiricalRuntimeReplayLane : AdapterAdvancementLane
  gate3SMClayReducerLane : AdapterAdvancementLane

data TokenReducerAdvancementLane : Set where
  numericAuthorityTokenIntakeLane : TokenReducerAdvancementLane
  maxwellHodgeSourceCalibrationLane : TokenReducerAdvancementLane
  quantumFiniteToGeneralBoundaryLane : TokenReducerAdvancementLane
  chemistrySpectroscopyAuthorityLane : TokenReducerAdvancementLane
  empiricalReplayAcceptanceLane : TokenReducerAdvancementLane
  clayProofTranslationLane : TokenReducerAdvancementLane

data ScopeResolutionLane : Set where
  finiteQuantumScopeLane : ScopeResolutionLane
  grAuthorityBoundaryLane : ScopeResolutionLane
  biologyFiniteScopeLane : ScopeResolutionLane
  chemistryFiniteRuleLane : ScopeResolutionLane
  empiricalRuntimeGovernanceLane : ScopeResolutionLane
  ymCompletionBoundaryLane : ScopeResolutionLane

data HardGateAdvancementLane : Set where
  nsMigrationThresholdConstantsLane : HardGateAdvancementLane
  ymExternalAcceptancePacketLane : HardGateAdvancementLane
  standardModelFiniteRepresentationLane : HardGateAdvancementLane
  maxwellHodgeSourceConservationLane : HardGateAdvancementLane
  numericMeasuredAuthorityNormalizationLane : HardGateAdvancementLane
  chemistryAuthorityBindingLane : HardGateAdvancementLane

data ClosureComputationLane : Set where
  nsSourceViscosityBalanceLane : ClosureComputationLane
  chemistryFiniteComputationLane : ClosureComputationLane
  standardModelFiniteAnomalyLane : ClosureComputationLane
  maxwellFiniteExteriorChainLane : ClosureComputationLane
  numericAuthorityPayloadValidatorLane : ClosureComputationLane
  finiteQuantumQFTScopedClosureLane : ClosureComputationLane

record PromotionLaneSummary : Set where
  field
    lane :
      PromotionImplementationLane

    ownerModule :
      String

    canonicalReceipt :
      String

    scope :
      String

    openObligationCount :
      Nat

    positiveBoundary :
      String

    falsePromotionGuards :
      String

    validationCommand :
      String

    promotesClaim :
      Bool

    promotesClaimIsFalse :
      promotesClaim ≡ false

open PromotionLaneSummary public

record AdapterAdvancementSummary : Set where
  field
    adapterLane :
      AdapterAdvancementLane

    adapterModule :
      String

    canonicalAdapter :
      String

    localAdvance :
      String

    remainingPromotionGap :
      String

    validationCommand :
      String

    promotesClaim :
      Bool

    promotesClaimIsFalse :
      promotesClaim ≡ false

open AdapterAdvancementSummary public

record TokenReducerAdvancementSummary : Set where
  field
    tokenLane :
      TokenReducerAdvancementLane

    tokenModule :
      String

    canonicalTokenSurface :
      String

    localAdvance :
      String

    nextCriticalGap :
      String

    validationCommand :
      String

    promotesClaim :
      Bool

    promotesClaimIsFalse :
      promotesClaim ≡ false

open TokenReducerAdvancementSummary public

record ScopeResolutionSummary : Set where
  field
    scopeLane :
      ScopeResolutionLane

    scopeModule :
      String

    canonicalScopeSurface :
      String

    resolvedPositiveBoundary :
      String

    remainingHardBoundary :
      String

    validationCommand :
      String

    promotesTerminalClaim :
      Bool

    promotesTerminalClaimIsFalse :
      promotesTerminalClaim ≡ false

open ScopeResolutionSummary public

record HardGateAdvancementSummary : Set where
  field
    hardGateLane :
      HardGateAdvancementLane

    hardGateModule :
      String

    canonicalHardGateSurface :
      String

    concreteAdvance :
      String

    remainingProofOrAuthorityGap :
      String

    validationCommand :
      String

    promotesClaim :
      Bool

    promotesClaimIsFalse :
      promotesClaim ≡ false

open HardGateAdvancementSummary public

record ClosureComputationSummary : Set where
  field
    closureLane :
      ClosureComputationLane

    closureModule :
      String

    canonicalClosureSurface :
      String

    concreteClosureAdvance :
      String

    remainingClosureGap :
      String

    validationCommand :
      String

    promotesClaim :
      Bool

    promotesClaimIsFalse :
      promotesClaim ≡ false

open ClosureComputationSummary public

mkLaneSummary :
  PromotionImplementationLane →
  String →
  String →
  String →
  Nat →
  String →
  String →
  String →
  PromotionLaneSummary
mkLaneSummary lane owner receipt scope count positive falseGuards command =
  record
    { lane = lane
    ; ownerModule = owner
    ; canonicalReceipt = receipt
    ; scope = scope
    ; openObligationCount = count
    ; positiveBoundary = positive
    ; falsePromotionGuards = falseGuards
    ; validationCommand = command
    ; promotesClaim = false
    ; promotesClaimIsFalse = refl
    }

mkAdapterAdvancementSummary :
  AdapterAdvancementLane →
  String →
  String →
  String →
  String →
  String →
  AdapterAdvancementSummary
mkAdapterAdvancementSummary lane owner adapter advance gap command =
  record
    { adapterLane = lane
    ; adapterModule = owner
    ; canonicalAdapter = adapter
    ; localAdvance = advance
    ; remainingPromotionGap = gap
    ; validationCommand = command
    ; promotesClaim = false
    ; promotesClaimIsFalse = refl
    }

mkTokenReducerAdvancementSummary :
  TokenReducerAdvancementLane →
  String →
  String →
  String →
  String →
  String →
  TokenReducerAdvancementSummary
mkTokenReducerAdvancementSummary lane owner surface advance gap command =
  record
    { tokenLane = lane
    ; tokenModule = owner
    ; canonicalTokenSurface = surface
    ; localAdvance = advance
    ; nextCriticalGap = gap
    ; validationCommand = command
    ; promotesClaim = false
    ; promotesClaimIsFalse = refl
    }

mkScopeResolutionSummary :
  ScopeResolutionLane →
  String →
  String →
  String →
  String →
  String →
  ScopeResolutionSummary
mkScopeResolutionSummary lane owner surface positive boundary command =
  record
    { scopeLane = lane
    ; scopeModule = owner
    ; canonicalScopeSurface = surface
    ; resolvedPositiveBoundary = positive
    ; remainingHardBoundary = boundary
    ; validationCommand = command
    ; promotesTerminalClaim = false
    ; promotesTerminalClaimIsFalse = refl
    }

mkHardGateAdvancementSummary :
  HardGateAdvancementLane →
  String →
  String →
  String →
  String →
  String →
  HardGateAdvancementSummary
mkHardGateAdvancementSummary lane owner surface advance gap command =
  record
    { hardGateLane = lane
    ; hardGateModule = owner
    ; canonicalHardGateSurface = surface
    ; concreteAdvance = advance
    ; remainingProofOrAuthorityGap = gap
    ; validationCommand = command
    ; promotesClaim = false
    ; promotesClaimIsFalse = refl
    }

mkClosureComputationSummary :
  ClosureComputationLane →
  String →
  String →
  String →
  String →
  String →
  ClosureComputationSummary
mkClosureComputationSummary lane owner surface advance gap command =
  record
    { closureLane = lane
    ; closureModule = owner
    ; canonicalClosureSurface = surface
    ; concreteClosureAdvance = advance
    ; remainingClosureGap = gap
    ; validationCommand = command
    ; promotesClaim = false
    ; promotesClaimIsFalse = refl
    }

canonicalPromotionLaneSummaries : List PromotionLaneSummary
canonicalPromotionLaneSummaries =
  mkLaneSummary
    numericAndAuthorityLane
    "DASHI.Promotion.NumericAndAuthorityObligations"
    "canonicalNumericAndAuthorityObligationIndex"
    "numeric measured values; provider authority; comparison law; covariance; holdout; runtime replay; semantic adequacy"
    9
    "authority and runtime metadata obligations are indexed"
    "numericValuePromoted/providerAuthority/comparison/covariance/holdout/replay/semantic adequacy remain false"
    "agda -i . DASHI/Promotion/NumericAndAuthorityObligations.agda"
  ∷ mkLaneSummary
    classicalFieldLane
    "DASHI.Promotion.ClassicalFieldObligations"
    "canonicalClassicalFieldPromotionObligationIndex"
    "physical laws; Maxwell field equations; GR field equations"
    3
    "classical field promotion stages are indexed"
    "physical laws, Maxwell, and GR promotion remain false"
    "agda -i . DASHI/Promotion/ClassicalFieldObligations.agda"
  ∷ mkLaneSummary
    quantumQFTLane
    "DASHI.Promotion.QuantumQFTObligations"
    "canonicalQuantumQFTPromotionObligationReceipt"
    "Schrodinger dynamics; Born semantics; QFT"
    14
    "quantum/QFT receipt targets are indexed against registry inputs"
    "Schrodinger dynamics, Born semantics, QFT, and quantum empirical adequacy remain false"
    "agda -i . DASHI/Promotion/QuantumQFTObligations.agda"
  ∷ mkLaneSummary
    chemistryBiologyLane
    "DASHI.Promotion.ChemistryBiologyObligations"
    "canonicalChemistryBiologyPromotionObligationIndex"
    "physical chemistry; spectroscopy; bonding; wet-lab chemistry; biology causation/intervention/clinical/brain-state recovery"
    11
    "chemistry and biology promotion obligations are indexed beyond local population receipts"
    "physical chemistry, spectroscopy, bonding, wet-lab, causation, intervention, clinical validity, and brain-state recovery remain false"
    "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
  ∷ mkLaneSummary
    gate3ClayLane
    "DASHI.Promotion.Gate3ClayObligations"
    "canonicalGate3ClayPromotionObligationReceipt"
    "Gate 3 closure; Mosco; no spectral pollution; mass shell; NS Clay; YM Clay"
    22
    "Gate 3 density evidence is recorded as non-promoting input"
    "Gate 3 closure, Mosco, no-pollution, transfer, mass-shell, NS Clay, YM Clay, and terminal Clay promotion remain false"
    "agda -i . DASHI/Promotion/Gate3ClayObligations.agda"
  ∷ mkLaneSummary
    standardModelTerminalLane
    "DASHI.Promotion.StandardModelTerminalObligations"
    "canonicalStandardModelTerminalPromotionObligationReceipt"
    "Standard Model; terminal/full unification"
    14
    "Standard Model and terminal claim-audit obligations are indexed"
    "Standard Model and terminal/full unification promotion remain false"
    "agda -i . DASHI/Promotion/StandardModelTerminalObligations.agda"
  ∷ []

canonicalAdapterAdvancementSummaries : List AdapterAdvancementSummary
canonicalAdapterAdvancementSummaries =
  mkAdapterAdvancementSummary
    measuredAuthorityAdapterLane
    "DASHI.Promotion.NumericMeasuredAuthorityBinding"
    "canonicalNumericMeasuredAuthorityBindingReceipt"
    "binds 9 measured constant slots to complete authority metadata and consumer-binding requirements"
    "accepted authority tokens and numeric value ingestion remain missing"
    "agda -i . DASHI/Promotion/NumericMeasuredAuthorityBinding.agda"
  ∷ mkAdapterAdvancementSummary
    maxwellExteriorCalculusLane
    "DASHI.Promotion.MaxwellExteriorCalculusAdapter"
    "canonicalMaxwellExteriorCalculusAdapter"
    "constructs the symbolic homogeneous Maxwell side F = dA and dF = 0"
    "metric/Hodge, source-current extraction, calibration, and empirical observable adapter remain missing"
    "agda -i . DASHI/Promotion/MaxwellExteriorCalculusAdapter.agda"
  ∷ mkAdapterAdvancementSummary
    finiteQuantumBornLane
    "DASHI.Promotion.FiniteQuantumSchrodingerBornAdapter"
    "canonicalFiniteQuantumSchrodingerBornAdapter"
    "inhabits a finite two-state identity evolution, zero Hamiltonian, and Born probability total"
    "full Hilbert domain, Stone theorem, continuum dynamics, POVM/statistical semantics, and QFT remain missing"
    "agda -i . DASHI/Promotion/FiniteQuantumSchrodingerBornAdapter.agda"
  ∷ mkAdapterAdvancementSummary
    chemistryQuantitativeLane
    "DASHI.Promotion.ChemistryQuantitativeAdapter"
    "canonicalChemistryQuantitativeAdapter"
    "adds stoichiometry, symbolic physical-chemistry law, spectroscopy, bonding, and wet-lab adapter fields"
    "measured authority, physical validation, bonding preservation proof, and replication acceptance remain missing"
    "agda -i . DASHI/Promotion/ChemistryQuantitativeAdapter.agda"
  ∷ mkAdapterAdvancementSummary
    empiricalRuntimeReplayLane
    "DASHI.Promotion.EmpiricalRuntimeReplayAdapter"
    "canonicalEmpiricalRuntimeValidationReport"
    "adds provider payload, observable, projection digest, comparison, covariance, holdout, replay, and semantic-review machinery"
    "provider authority, comparison law, covariance authority, holdout acceptance, replay authority, and semantic adequacy remain missing"
    "agda -i . DASHI/Promotion/EmpiricalRuntimeReplayAdapter.agda"
  ∷ mkAdapterAdvancementSummary
    gate3SMClayReducerLane
    "DASHI.Promotion.Gate3StandardModelClayEvidenceReducer"
    "canonicalGate3StandardModelClayEvidenceReducer"
    "classifies 35 Gate3, Standard Model, NS, YM, and terminal evidence rows"
    "H11/8 is a Clay-equivalent hard-open target; Sprint145 comparison envelope is failed/closed; MaximumLocationMigrationLemma is active"
    "agda -i . DASHI/Promotion/Gate3StandardModelClayEvidenceReducer.agda"
  ∷ []

canonicalTokenReducerAdvancementSummaries :
  List TokenReducerAdvancementSummary
canonicalTokenReducerAdvancementSummaries =
  mkTokenReducerAdvancementSummary
    numericAuthorityTokenIntakeLane
    "DASHI.Promotion.NumericAuthorityTokenIntake"
    "canonicalNumericAuthorityTokenIntakeReceipt"
    "populates 9 authority-token requests over measured constants with explicit missing-token states"
    "accepted authority tokens and value-ingestion receipts remain missing"
    "agda -i . DASHI/Promotion/NumericAuthorityTokenIntake.agda"
  ∷ mkTokenReducerAdvancementSummary
    maxwellHodgeSourceCalibrationLane
    "DASHI.Promotion.MaxwellHodgeSourceCalibration"
    "canonicalMaxwellHodgeSourceCalibration"
    "classifies 6 Maxwell Hodge/source calibration inputs and selects nextHodgeStarAuthority"
    "accepted Hodge authority, source-current proof, continuity proof, and empirical observable authority remain missing"
    "agda -i . DASHI/Promotion/MaxwellHodgeSourceCalibration.agda"
  ∷ mkTokenReducerAdvancementSummary
    quantumFiniteToGeneralBoundaryLane
    "DASHI.Promotion.QuantumFiniteToGeneralBoundary"
    "canonicalQuantumFiniteToGeneralBoundary"
    "separates one finite quantum evidence row from 8 full-lift obligations"
    "dense Hilbert domain, unbounded/self-adjoint Hamiltonian, Stone theorem, POVM, repeated-measure, and empirical calibration remain missing"
    "agda -i . DASHI/Promotion/QuantumFiniteToGeneralBoundary.agda"
  ∷ mkTokenReducerAdvancementSummary
    chemistrySpectroscopyAuthorityLane
    "DASHI.Promotion.ChemistrySpectroscopyAuthorityIntake"
    "canonicalChemistrySpectroscopyAuthorityIntake"
    "populates 10 chemistry/spectroscopy authority requests with missing/unvalidated status"
    "accepted chemistry authority tokens and validation receipts remain missing"
    "agda -i . DASHI/Promotion/ChemistrySpectroscopyAuthorityIntake.agda"
  ∷ mkTokenReducerAdvancementSummary
    empiricalReplayAcceptanceLane
    "DASHI.Promotion.EmpiricalReplayAcceptanceCriteria"
    "canonicalEmpiricalReplayAcceptanceEvaluation"
    "evaluates 10 replay acceptance criteria with 2 local passes and 8 fail-closed authority criteria"
    "provider, observable, transform, comparison, covariance, holdout, parser/reducer, and semantic-review authorities remain missing"
    "agda -i . DASHI/Promotion/EmpiricalReplayAcceptanceCriteria.agda"
  ∷ mkTokenReducerAdvancementSummary
    clayProofTranslationLane
    "DASHI.Promotion.ClayProofTranslationReducer"
    "canonicalClayProofTranslationReducer"
    "adds 11 Clay proof/translation rows and selects MaximumLocationMigrationLemma as the active Hou-Luo proof gate"
    "actual Hou-Luo migration proof discharge, accepted authority, and known-physics translation remain missing"
    "agda -i . DASHI/Promotion/ClayProofTranslationReducer.agda"
  ∷ []

canonicalScopeResolutionSummaries : List ScopeResolutionSummary
canonicalScopeResolutionSummaries =
  mkScopeResolutionSummary
    finiteQuantumScopeLane
    "DASHI.Promotion.FiniteQuantumPhysicalScopeDecision"
    "canonicalFiniteQuantumPhysicalScopeDecision"
    "finite-mode Schrodinger/Born computation is sufficient for finite carrier calculations"
    "infinite Hilbert completion, unbounded operators, Stone/spectral calculus, general Born semantics, QFT, and empirical calibration remain false"
    "agda -i . DASHI/Promotion/FiniteQuantumPhysicalScopeDecision.agda"
  ∷ mkScopeResolutionSummary
    grAuthorityBoundaryLane
    "DASHI.Promotion.GRBoundaryClarification"
    "canonicalGRBoundaryClarificationIndex"
    "Minkowski/flat tangent recovery may be used internally under bounded known-limit scope"
    "non-flat Einstein equations, Bianchi identity, stress-energy coupling, Schwarzschild, cosmology, and continuum GR remain authority/adapter blocked"
    "agda -i . DASHI/Promotion/GRBoundaryClarification.agda"
  ∷ mkScopeResolutionSummary
    biologyFiniteScopeLane
    "DASHI.Promotion.BiologyFiniteScopeClarification"
    "canonicalBiologyFiniteScopeClarification"
    "finite genetic-code, protein-symbol, supervoxel, streaming, and checksum structure is populated"
    "biological causation, intervention, clinical validity, genome-to-connectome closure, and brain-state recovery remain external-authority blocked"
    "agda -i . DASHI/Promotion/BiologyFiniteScopeClarification.agda"
  ∷ mkScopeResolutionSummary
    chemistryFiniteRuleLane
    "DASHI.Promotion.ChemistryFiniteRuleTargets"
    "canonicalChemistryFiniteRuleTargets"
    "first-ten-element Aufbau/Pauli/Hund targets plus Rydberg and Gibbs formula slots are populated"
    "measured constants, spectra, thermochemistry, physical chemistry promotion, and wet-lab validation remain authority gated"
    "agda -i . DASHI/Promotion/ChemistryFiniteRuleTargets.agda"
  ∷ mkScopeResolutionSummary
    empiricalRuntimeGovernanceLane
    "DASHI.Promotion.EmpiricalReplayAcceptanceCriteria"
    "canonicalEmpiricalReplayInfrastructureTokenSummary"
    "provider, covariant chi-square, covariance, holdout, replay, and semantic-review infrastructure gates are populated"
    "all six empirical/runtime acceptance tokens remain false"
    "agda -i . DASHI/Promotion/EmpiricalReplayAcceptanceCriteria.agda"
  ∷ mkScopeResolutionSummary
    ymCompletionBoundaryLane
    "DASHI.Physics.Closure.YMCompletionBoundaryTightening"
    "ymCompletionBoundaryStatus"
    "YM finite/support/lattice/small-field/thermodynamic/OS/Wightman/continuum-transfer/survival lanes are authority-conditionally advanced"
    "external acceptance, all-provider derivation, Clay statement discharge, and Clay YM promotion remain false"
    "agda -i . -l standard-library DASHI/Physics/Closure/YMCompletionBoundaryTightening.agda"
  ∷ []

canonicalHardGateAdvancementSummaries : List HardGateAdvancementSummary
canonicalHardGateAdvancementSummaries =
  mkHardGateAdvancementSummary
    nsMigrationThresholdConstantsLane
    "DASHI.Physics.Closure.NSMigrationInitiationThresholdConstantsReceipt"
    "canonicalNSMigrationInitiationThresholdConstantsReceipt"
    "normalizes seven source/viscosity/off-axis/log constants, four inequality directions, five required estimates, and five fail-closed flags"
    "source-integral lower bound, retained-viscosity lower bound, off-axis gain absorption, log-feedback absorption, and large-data uniformity remain unproved"
    "agda -i . -i DCHoTT-Agda -i cubical DASHI/Physics/Closure/NSMigrationInitiationThresholdConstantsReceipt.agda"
  ∷ mkHardGateAdvancementSummary
    ymExternalAcceptancePacketLane
    "DASHI.Physics.Closure.YMExternalAcceptancePacketNormalization"
    "canonicalYMExternalAcceptancePacketNormalization"
    "normalizes six external authority tokens, five reproducibility artifacts, eight packet components, and six false-promotion guards"
    "external governance completion, external acceptance token, Clay statement boundary discharge, and Clay promotion remain false"
    "agda -i . -l standard-library DASHI/Physics/Closure/YMExternalAcceptancePacketNormalization.agda"
  ∷ mkHardGateAdvancementSummary
    standardModelFiniteRepresentationLane
    "DASHI.Promotion.StandardModelFiniteRepresentationNarrowing"
    "canonicalStandardModelFiniteRepresentationNarrowingReceipt"
    "narrows the SM lane to three finite gauge rows, p2/p3/p5 surfaces, five one-generation targets, and five conductor hypercharge rows"
    "continuous gauge bridge, exact physical representation content, PDG/empirical authority, and broad SM promotion remain false"
    "agda -i . DASHI/Promotion/StandardModelFiniteRepresentationNarrowing.agda"
  ∷ mkHardGateAdvancementSummary
    maxwellHodgeSourceConservationLane
    "DASHI.Promotion.MaxwellHodgeSourceConservationObligations"
    "canonicalMaxwellHodgeSourceConservationClosure"
    "normalizes ten Maxwell Hodge/source conservation rows covering metric, Hodge star, J, d*F=J, dJ=0, divJ=0, unit calibration, and empirical observables"
    "Hodge authority, source-current proof, inhomogeneous equation proof, source conservation proof, calibration, empirical authority, and Maxwell promotion remain false"
    "agda -i . DASHI/Promotion/MaxwellHodgeSourceConservationObligations.agda"
  ∷ mkHardGateAdvancementSummary
    numericMeasuredAuthorityNormalizationLane
    "DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization"
    "canonicalNormalizedMeasuredAuthorityTokenReceipt"
    "normalizes eighteen measured authority tokens across CODATA, PDG, CODATA/PDG, mass, electromagnetic-vacuum, and particle/SM families with seven required metadata fields"
    "accepted authority token, numeric value ingestion, and numeric promotion remain false"
    "agda -i . DASHI/Promotion/NumericMeasuredAuthorityTokenNormalization.agda"
  ∷ mkHardGateAdvancementSummary
    chemistryAuthorityBindingLane
    "DASHI.Promotion.ChemistryAuthorityBinding"
    "canonicalChemistryAuthorityBinding"
    "binds three chemistry authority tokens, three spectral-line rows, four thermochemistry rows, two calibration rows, and four provenance rows"
    "accepted chemistry authority tokens, calibration, uncertainty/provenance acceptance, physical chemistry, spectroscopy, and wet-lab promotion remain false"
    "agda -i . DASHI/Promotion/ChemistryAuthorityBinding.agda"
  ∷ []

canonicalClosureComputationSummaries :
  List ClosureComputationSummary
canonicalClosureComputationSummaries =
  mkClosureComputationSummary
    nsSourceViscosityBalanceLane
    "DASHI.Physics.Closure.NSSprint150SourceViscosityBalanceReceipt"
    "canonicalNSSprint150SourceViscosityBalanceReceipt"
    "decomposes Sprint 150 source/viscosity balance into eight source components, seven viscosity components, nine analytic lemmas, six inequality rows, eight blockers, and seven false-promotion guards"
    "source-integral lower bound, retained-viscosity lower bound, localized source-beats-viscosity balance, scaling consistency, BKM finiteness, and NS Clay remain false"
    "agda -i . -i DCHoTT-Agda -i cubical DASHI/Physics/Closure/NSSprint150SourceViscosityBalanceReceipt.agda && pytest -q tests/test_ns_sprint150_source_viscosity_balance.py"
  ∷ mkClosureComputationSummary
    chemistryFiniteComputationLane
    "DASHI.Promotion.ChemistryFiniteComputationSurface"
    "canonicalChemistryFiniteComputationSurface"
    "checks first-eighteen Aufbau occupations, Pauli capacities, Hund multiplicities, six Rydberg rational projections, and five Gibbs integer projections"
    "measured authority, spectroscopy, thermochemistry, bonding interpretation, physical chemistry, and wet-lab validation remain false"
    "agda -i . DASHI/Promotion/ChemistryFiniteComputationSurface.agda"
  ∷ mkClosureComputationSummary
    standardModelFiniteAnomalyLane
    "DASHI.Promotion.StandardModelFiniteAnomalyHyperchargeCheck"
    "canonicalFiniteSMAnomalyHyperchargeCheckReceipt"
    "checks finite one-generation all-left-handed Weyl hypercharge rows and four anomaly numerator-zero rows under the existing normalization receipts"
    "continuous gauge construction, exact physical irreps, PDG/empirical authority, broad Standard Model, and terminal unification remain false"
    "agda -i . -l standard-library DASHI/Promotion/StandardModelFiniteAnomalyHyperchargeCheck.agda"
  ∷ mkClosureComputationSummary
    maxwellFiniteExteriorChainLane
    "DASHI.Promotion.MaxwellFiniteExteriorChainStrengthening"
    "canonicalMaxwellFiniteExteriorChainStrengthening"
    "records thirteen finite exterior-chain rows from A, F=dA, dF=0 through Hodge, J, d*F=J, dJ=0, divJ=0, units, observables, and promotion guard"
    "metric/Hodge authority, source extraction, inhomogeneous equation proof, conservation proof, calibration, empirical authority, and Maxwell promotion remain false"
    "agda -i . DASHI/Promotion/MaxwellFiniteExteriorChainStrengthening.agda"
  ∷ mkClosureComputationSummary
    numericAuthorityPayloadValidatorLane
    "DASHI.Promotion.NumericAuthorityPayloadValidator"
    "canonicalNumericAuthorityPayloadValidatorReceipt"
    "normalizes twenty payload schema fields, three source-family coverage rows, eighteen payload envelopes, and zero accepted/loaded payloads"
    "external authority artifact bytes, checksum, raw value text, uncertainty, covariance, consumer ingestion, loaded values, and numeric promotion remain false"
    "agda -i . DASHI/Promotion/NumericAuthorityPayloadValidator.agda"
  ∷ mkClosureComputationSummary
    finiteQuantumQFTScopedClosureLane
    "DASHI.Promotion.FiniteQuantumQFTScopedClosure"
    "canonicalFiniteQuantumQFTScopedClosure"
    "closes finite-mode quantum over two Hilbert rows, two identity-evolution rows, one zero-Hamiltonian row, four observable probability rows, and two Born normalization rows"
    "infinite Hilbert completion, Stone theorem, spectral theorem, general Born semantics, QFT, and terminal quantum promotion remain false"
    "agda -i . DASHI/Promotion/FiniteQuantumQFTScopedClosure.agda"
  ∷ []

record UnifiedPromotionObligationIndex : Setω where
  field
    sourceKnownInputsPopulation :
      Registry.KnownInputsPopulationReceipt

    sourceCategoricalInterlink :
      Interlink.CategoricalInterlinkReceipt

    numericAndAuthority :
      Numeric.NumericAndAuthorityObligationIndex

    classicalField :
      Classical.ClassicalFieldPromotionObligationIndex

    quantumQFT :
      Quantum.QuantumQFTPromotionObligationReceipt

    chemistryBiology :
      ChemBio.ChemistryBiologyPromotionObligationIndex

    gate3Clay :
      GateClay.Gate3ClayPromotionObligationReceipt

    standardModelTerminal :
      SMT.StandardModelTerminalPromotionObligationReceipt

    measuredAuthorityBinding :
      Measured.NumericMeasuredAuthorityBindingReceipt

    maxwellExteriorCalculus :
      Maxwell.MaxwellExteriorCalculusAdapter

    finiteQuantumSchrodingerBorn :
      FiniteQuantum.FiniteQuantumSchrodingerBornAdapter

    chemistryQuantitativeAdapter :
      ChemistryAdapter.ChemistryQuantitativeAdapter

    empiricalRuntimeValidationReport :
      RuntimeAdapter.EmpiricalRuntimeValidationReport

    gate3StandardModelClayEvidenceReducer :
      Reducer.Gate3StandardModelClayEvidenceReducer

    numericAuthorityTokenIntake :
      NumericIntake.NumericAuthorityTokenIntakeReceipt

    maxwellHodgeSourceCalibration :
      MaxwellCalibration.MaxwellHodgeSourceCalibration

    quantumFiniteToGeneralBoundary :
      QuantumBoundary.QuantumFiniteToGeneralBoundary

    chemistrySpectroscopyAuthorityIntake :
      ChemAuthority.ChemistrySpectroscopyAuthorityIntake

    empiricalReplayAcceptanceEvaluation :
      ReplayCriteria.EmpiricalReplayAcceptanceEvaluation

    clayProofTranslationReducer :
      ClayTranslation.ClayProofTranslationReducer

    finiteQuantumPhysicalScopeDecision :
      QuantumScope.FiniteQuantumPhysicalScopeDecision

    grBoundaryClarification :
      GRScope.GRBoundaryClarificationIndex

    biologyFiniteScopeClarification :
      BiologyScope.BiologyFiniteScopeClarification

    chemistryFiniteRuleTargets :
      ChemistryRules.ChemistryFiniteRuleTargets

    empiricalReplayInfrastructureTokenSummary :
      ReplayCriteria.EmpiricalReplayInfrastructureTokenSummary

    ymCompletionBoundaryStatus :
      YMScope.YMCompletionBoundaryStatus

    nsMigrationInitiationThresholdConstants :
      NSConstants.NSMigrationInitiationThresholdConstantsReceipt

    ymExternalAcceptancePacketNormalization :
      YMExternal.YMExternalAcceptancePacketNormalization

    standardModelFiniteRepresentationNarrowing :
      SMNarrowing.StandardModelFiniteRepresentationNarrowingReceipt

    maxwellHodgeSourceConservationClosure :
      MaxwellConservation.MaxwellHodgeSourceConservationClosure

    normalizedMeasuredAuthorityTokenReceipt :
      NumericNormalization.NormalizedMeasuredAuthorityTokenReceipt

    chemistryAuthorityBinding :
      ChemistryBinding.ChemistryAuthorityBinding

    nsSprint150SourceViscosityBalance :
      NS150.NSSprint150SourceViscosityBalanceReceipt

    chemistryFiniteComputationSurface :
      ChemistryComputation.ChemistryFiniteComputationSurface

    standardModelFiniteAnomalyHyperchargeCheck :
      SMAnomaly.FiniteSMAnomalyHyperchargeCheckReceipt

    maxwellFiniteExteriorChainStrengthening :
      MaxwellChain.MaxwellFiniteExteriorChainStrengthening

    numericAuthorityPayloadValidator :
      NumericPayload.NumericAuthorityPayloadValidatorReceipt

    finiteQuantumQFTScopedClosure :
      QuantumClosure.FiniteQuantumQFTScopedClosure

    laneSummaries :
      List PromotionLaneSummary

    adapterAdvancementSummaries :
      List AdapterAdvancementSummary

    tokenReducerAdvancementSummaries :
      List TokenReducerAdvancementSummary

    scopeResolutionSummaries :
      List ScopeResolutionSummary

    hardGateAdvancementSummaries :
      List HardGateAdvancementSummary

    closureComputationSummaries :
      List ClosureComputationSummary

    laneSummaryCount :
      Nat

    laneSummaryCountIs6 :
      laneSummaryCount ≡ 6

    adapterAdvancementCount :
      Nat

    adapterAdvancementCountIs6 :
      adapterAdvancementCount ≡ 6

    tokenReducerAdvancementCount :
      Nat

    tokenReducerAdvancementCountIs6 :
      tokenReducerAdvancementCount ≡ 6

    scopeResolutionCount :
      Nat

    scopeResolutionCountIs6 :
      scopeResolutionCount ≡ 6

    hardGateAdvancementCount :
      Nat

    hardGateAdvancementCountIs6 :
      hardGateAdvancementCount ≡ 6

    closureComputationCount :
      Nat

    closureComputationCountIs6 :
      closureComputationCount ≡ 6

    aggregateOpenObligationCount :
      Nat

    aggregateOpenObligationCountIs73 :
      aggregateOpenObligationCount ≡ 73

    validationTarget :
      String

    validationCommand :
      String

    allPromotionGuardsStillFalse :
      Bool

    allPromotionGuardsStillFalseIsTrue :
      allPromotionGuardsStillFalse ≡ true

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

open UnifiedPromotionObligationIndex public

canonicalUnifiedPromotionObligationIndex :
  UnifiedPromotionObligationIndex
canonicalUnifiedPromotionObligationIndex =
  record
    { sourceKnownInputsPopulation =
        Registry.canonicalKnownInputsPopulationReceipt
    ; sourceCategoricalInterlink =
        Interlink.canonicalCategoricalInterlinkReceipt
    ; numericAndAuthority =
        Numeric.canonicalNumericAndAuthorityObligationIndex
    ; classicalField =
        Classical.canonicalClassicalFieldPromotionObligationIndex
    ; quantumQFT =
        Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; chemistryBiology =
        ChemBio.canonicalChemistryBiologyPromotionObligationIndex
    ; gate3Clay =
        GateClay.canonicalGate3ClayPromotionObligationReceipt
    ; standardModelTerminal =
        SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; measuredAuthorityBinding =
        Measured.canonicalNumericMeasuredAuthorityBindingReceipt
    ; maxwellExteriorCalculus =
        Maxwell.canonicalMaxwellExteriorCalculusAdapter
    ; finiteQuantumSchrodingerBorn =
        FiniteQuantum.canonicalFiniteQuantumSchrodingerBornAdapter
    ; chemistryQuantitativeAdapter =
        ChemistryAdapter.canonicalChemistryQuantitativeAdapter
    ; empiricalRuntimeValidationReport =
        RuntimeAdapter.canonicalEmpiricalRuntimeValidationReport
    ; gate3StandardModelClayEvidenceReducer =
        Reducer.canonicalGate3StandardModelClayEvidenceReducer
    ; numericAuthorityTokenIntake =
        NumericIntake.canonicalNumericAuthorityTokenIntakeReceipt
    ; maxwellHodgeSourceCalibration =
        MaxwellCalibration.canonicalMaxwellHodgeSourceCalibration
    ; quantumFiniteToGeneralBoundary =
        QuantumBoundary.canonicalQuantumFiniteToGeneralBoundary
    ; chemistrySpectroscopyAuthorityIntake =
        ChemAuthority.canonicalChemistrySpectroscopyAuthorityIntake
    ; empiricalReplayAcceptanceEvaluation =
        ReplayCriteria.canonicalEmpiricalReplayAcceptanceEvaluation
    ; clayProofTranslationReducer =
        ClayTranslation.canonicalClayProofTranslationReducer
    ; finiteQuantumPhysicalScopeDecision =
        QuantumScope.canonicalFiniteQuantumPhysicalScopeDecision
    ; grBoundaryClarification =
        GRScope.canonicalGRBoundaryClarificationIndex
    ; biologyFiniteScopeClarification =
        BiologyScope.canonicalBiologyFiniteScopeClarification
    ; chemistryFiniteRuleTargets =
        ChemistryRules.canonicalChemistryFiniteRuleTargets
    ; empiricalReplayInfrastructureTokenSummary =
        ReplayCriteria.canonicalEmpiricalReplayInfrastructureTokenSummary
    ; ymCompletionBoundaryStatus =
        YMScope.ymCompletionBoundaryStatus
    ; nsMigrationInitiationThresholdConstants =
        NSConstants.canonicalNSMigrationInitiationThresholdConstantsReceipt
    ; ymExternalAcceptancePacketNormalization =
        YMExternal.canonicalYMExternalAcceptancePacketNormalization
    ; standardModelFiniteRepresentationNarrowing =
        SMNarrowing.canonicalStandardModelFiniteRepresentationNarrowingReceipt
    ; maxwellHodgeSourceConservationClosure =
        MaxwellConservation.canonicalMaxwellHodgeSourceConservationClosure
    ; normalizedMeasuredAuthorityTokenReceipt =
        NumericNormalization.canonicalNormalizedMeasuredAuthorityTokenReceipt
    ; chemistryAuthorityBinding =
        ChemistryBinding.canonicalChemistryAuthorityBinding
    ; nsSprint150SourceViscosityBalance =
        NS150.canonicalNSSprint150SourceViscosityBalanceReceipt
    ; chemistryFiniteComputationSurface =
        ChemistryComputation.canonicalChemistryFiniteComputationSurface
    ; standardModelFiniteAnomalyHyperchargeCheck =
        SMAnomaly.canonicalFiniteSMAnomalyHyperchargeCheckReceipt
    ; maxwellFiniteExteriorChainStrengthening =
        MaxwellChain.canonicalMaxwellFiniteExteriorChainStrengthening
    ; numericAuthorityPayloadValidator =
        NumericPayload.canonicalNumericAuthorityPayloadValidatorReceipt
    ; finiteQuantumQFTScopedClosure =
        QuantumClosure.canonicalFiniteQuantumQFTScopedClosure
    ; laneSummaries =
        canonicalPromotionLaneSummaries
    ; adapterAdvancementSummaries =
        canonicalAdapterAdvancementSummaries
    ; tokenReducerAdvancementSummaries =
        canonicalTokenReducerAdvancementSummaries
    ; scopeResolutionSummaries =
        canonicalScopeResolutionSummaries
    ; hardGateAdvancementSummaries =
        canonicalHardGateAdvancementSummaries
    ; closureComputationSummaries =
        canonicalClosureComputationSummaries
    ; laneSummaryCount =
        6
    ; laneSummaryCountIs6 =
        refl
    ; adapterAdvancementCount =
        6
    ; adapterAdvancementCountIs6 =
        refl
    ; tokenReducerAdvancementCount =
        6
    ; tokenReducerAdvancementCountIs6 =
        refl
    ; scopeResolutionCount =
        6
    ; scopeResolutionCountIs6 =
        refl
    ; hardGateAdvancementCount =
        6
    ; hardGateAdvancementCountIs6 =
        refl
    ; closureComputationCount =
        6
    ; closureComputationCountIs6 =
        refl
    ; aggregateOpenObligationCount =
        73
    ; aggregateOpenObligationCountIs73 =
        refl
    ; validationTarget =
        "DASHI/Promotion/ObligationIndex.agda"
    ; validationCommand =
        "agda -i . DASHI/Promotion/ObligationIndex.agda"
    ; allPromotionGuardsStillFalse =
        true
    ; allPromotionGuardsStillFalseIsTrue =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    }

canonicalUnifiedPromotionLaneCountIs6 :
  UnifiedPromotionObligationIndex.laneSummaryCount
    canonicalUnifiedPromotionObligationIndex
  ≡ 6
canonicalUnifiedPromotionLaneCountIs6 = refl

canonicalUnifiedPromotionOpenObligationCountIs73 :
  UnifiedPromotionObligationIndex.aggregateOpenObligationCount
    canonicalUnifiedPromotionObligationIndex
  ≡ 73
canonicalUnifiedPromotionOpenObligationCountIs73 = refl

canonicalUnifiedPromotionAdapterAdvancementCountIs6 :
  UnifiedPromotionObligationIndex.adapterAdvancementCount
    canonicalUnifiedPromotionObligationIndex
  ≡ 6
canonicalUnifiedPromotionAdapterAdvancementCountIs6 = refl

canonicalUnifiedPromotionTokenReducerAdvancementCountIs6 :
  UnifiedPromotionObligationIndex.tokenReducerAdvancementCount
    canonicalUnifiedPromotionObligationIndex
  ≡ 6
canonicalUnifiedPromotionTokenReducerAdvancementCountIs6 = refl

canonicalUnifiedPromotionScopeResolutionCountIs6 :
  UnifiedPromotionObligationIndex.scopeResolutionCount
    canonicalUnifiedPromotionObligationIndex
  ≡ 6
canonicalUnifiedPromotionScopeResolutionCountIs6 = refl

canonicalUnifiedPromotionHardGateAdvancementCountIs6 :
  UnifiedPromotionObligationIndex.hardGateAdvancementCount
    canonicalUnifiedPromotionObligationIndex
  ≡ 6
canonicalUnifiedPromotionHardGateAdvancementCountIs6 = refl

canonicalUnifiedPromotionClosureComputationCountIs6 :
  UnifiedPromotionObligationIndex.closureComputationCount
    canonicalUnifiedPromotionObligationIndex
  ≡ 6
canonicalUnifiedPromotionClosureComputationCountIs6 = refl

canonicalUnifiedPromotionTerminalPromotionIsFalse :
  UnifiedPromotionObligationIndex.terminalPromotion
    canonicalUnifiedPromotionObligationIndex
  ≡ false
canonicalUnifiedPromotionTerminalPromotionIsFalse = refl
