module DASHI.Interop.CategoricalInterlinkLayer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Constants.Registry as Registry

------------------------------------------------------------------------
-- Systematic lane interlink and promotion map.
--
-- This module is a typed receipt graph.  It records how populated constants,
-- law targets, authorities, and lane receipts are allowed to point at one
-- another.  It does not assert formal functoriality unless the cited owner
-- module already owns that claim, and it does not promote physics, Clay,
-- empirical, chemistry, biology, or runtime adequacy by itself.

data LaneFamily : Set where
  constantsMetrologyLane : LaneFamily
  quantumLane : LaneFamily
  qftStandardModelLane : LaneFamily
  chemistryLane : LaneFamily
  biologyDNABrainLane : LaneFamily
  maxwellGaugeLane : LaneFamily
  grLane : LaneFamily
  empiricalLane : LaneFamily
  runtimePNFLane : LaneFamily
  gate3ArithmeticLane : LaneFamily
  navierStokesLane : LaneFamily
  yangMillsLane : LaneFamily

data PromotionStage : Set where
  s0CarrierNamed : PromotionStage
  s1BoundedObservable : PromotionStage
  s2FormalReceipt : PromotionStage
  s3FailClosedGuard : PromotionStage
  s4AdapterReceiptConsumed : PromotionStage
  s5ProofOrAuthorityTokenInhabited : PromotionStage
  s6ClaimSurfaceUpdatedAfterValidation : PromotionStage

data PromotionClass : Set where
  exactReferenceInputPromoted : PromotionClass
  externalAuthoritySlotPromoted : PromotionClass
  typedSurfaceOnlyPromoted : PromotionClass
  finiteCategoricalReceiptPromoted : PromotionClass
  localDefinitionalReceiptPromoted : PromotionClass
  conditionalOnExternalAuthority : PromotionClass
  routeEvidenceOnlyPromoted : PromotionClass
  physicalPromotionFalse : PromotionClass

data InterlinkEdgeKind : Set where
  owns : InterlinkEdgeKind
  cites : InterlinkEdgeKind
  consumes : InterlinkEdgeKind
  blocks : InterlinkEdgeKind
  validates : InterlinkEdgeKind
  externalAuthorityRequired : InterlinkEdgeKind

record LaneObjectSlot : Set₁ where
  field
    laneLabel : String
    family : LaneFamily
    carrierObject : String
    ownerModule : String
    canonicalReceipt : String
    promotionStage : PromotionStage
    promotionClass : PromotionClass
    theoremPromoted : Bool
    theoremPromotedIsFalse : theoremPromoted ≡ false
    boundaryNotes : List String

open LaneObjectSlot public

record LaneMorphismSlot : Set₁ where
  field
    morphismLabel : String
    sourceLane : String
    targetLane : String
    edgeKind : InterlinkEdgeKind
    routeOrAdapter : String
    requiredBlockers : List String
    claimPromoted : Bool
    claimPromotedIsFalse : claimPromoted ≡ false

open LaneMorphismSlot public

record RegistryLaneBinding : Set₁ where
  field
    bindingLabel : String
    registrySlotFamily : String
    consumingLane : String
    consumingReceipt : String
    promotionClass : PromotionClass
    requiredAdapterPolicy : List String
    claimPromoted : Bool
    claimPromotedIsFalse : claimPromoted ≡ false

open RegistryLaneBinding public

record PromotionLadderRow : Set where
  field
    stage : PromotionStage
    stageLabel : String
    requiredEvidence : String
    promotionReading : String

open PromotionLadderRow public

mkLaneObject :
  String →
  LaneFamily →
  String →
  String →
  String →
  PromotionStage →
  PromotionClass →
  List String →
  LaneObjectSlot
mkLaneObject label family carrier owner receipt stage promotion notes =
  record
    { laneLabel = label
    ; family = family
    ; carrierObject = carrier
    ; ownerModule = owner
    ; canonicalReceipt = receipt
    ; promotionStage = stage
    ; promotionClass = promotion
    ; theoremPromoted = false
    ; theoremPromotedIsFalse = refl
    ; boundaryNotes = notes
    }

mkMorphism :
  String →
  String →
  String →
  InterlinkEdgeKind →
  String →
  List String →
  LaneMorphismSlot
mkMorphism label source target edge adapter blockers =
  record
    { morphismLabel = label
    ; sourceLane = source
    ; targetLane = target
    ; edgeKind = edge
    ; routeOrAdapter = adapter
    ; requiredBlockers = blockers
    ; claimPromoted = false
    ; claimPromotedIsFalse = refl
    }

mkRegistryBinding :
  String →
  String →
  String →
  String →
  PromotionClass →
  List String →
  RegistryLaneBinding
mkRegistryBinding label slot lane receipt promotion policy =
  record
    { bindingLabel = label
    ; registrySlotFamily = slot
    ; consumingLane = lane
    ; consumingReceipt = receipt
    ; promotionClass = promotion
    ; requiredAdapterPolicy = policy
    ; claimPromoted = false
    ; claimPromotedIsFalse = refl
    }

mkLadder :
  PromotionStage →
  String →
  String →
  String →
  PromotionLadderRow
mkLadder stage label evidence reading =
  record
    { stage = stage
    ; stageLabel = label
    ; requiredEvidence = evidence
    ; promotionReading = reading
    }

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

canonicalPromotionLadder : List PromotionLadderRow
canonicalPromotionLadder =
  mkLadder
    s0CarrierNamed
    "S0 carrier named"
    "lane has a named carrier, owner, and target vocabulary"
    "not a theorem claim"
  ∷ mkLadder
    s1BoundedObservable
    "S1 bounded observable"
    "observable or theorem target is bounded enough to cite"
    "target is inspectable but not validated"
  ∷ mkLadder
    s2FormalReceipt
    "S2 executable/formal receipt"
    "Agda receipt, script output, or provider receipt exists"
    "receipt exists but can still be non-promoting"
  ∷ mkLadder
    s3FailClosedGuard
    "S3 fail-closed Agda guard"
    "claim guard is false by construction or impossible without token"
    "safe for repo-wide citation"
  ∷ mkLadder
    s4AdapterReceiptConsumed
    "S4 adapter receipt consumed"
    "required adapter/source/version/checksum receipt is consumed"
    "local adapter can be promoted, not the global theorem"
  ∷ mkLadder
    s5ProofOrAuthorityTokenInhabited
    "S5 proof/authority token inhabited"
    "the needed proof object or accepted authority token exists"
    "claim may be reviewed for promotion"
  ∷ mkLadder
    s6ClaimSurfaceUpdatedAfterValidation
    "S6 claim surface updated after validation"
    "docs, Agda owner, validation target, and changelog agree"
    "only this stage changes the user-facing claim"
  ∷ []

canonicalLaneObjects : List LaneObjectSlot
canonicalLaneObjects =
  mkLaneObject
    "constants and SI metrology"
    constantsMetrologyLane
    "KnownConstantSlot / KnownLawSlot / AuthoritySourceSlot"
    "DASHI.Constants.Registry"
    "canonicalKnownInputsPopulationReceipt"
    s3FailClosedGuard
    exactReferenceInputPromoted
    ( "40 known constant slots, 33 law slots, and 11 authority slots"
    ∷ "external-input-only; no carrier derivation"
    ∷ []
    )
  ∷ mkLaneObject
    "Schrodinger and quantum measurement"
    quantumLane
    "Hilbert/measurement/QM target vocabulary"
    "DASHI.Constants.Registry"
    "canonicalQuantumKnownInputsReferenceReceipt"
    s3FailClosedGuard
    typedSurfaceOnlyPromoted
    ( "h, hbar, c, and e are reference inputs only"
    ∷ "dynamics, Born semantics, QFT, and empirical adequacy remain false"
    ∷ []
    )
  ∷ mkLaneObject
    "QFT, DHR, and Standard Model sector"
    qftStandardModelLane
    "finite prime-lane categorical receipts"
    "DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt"
    "canonicalConditionalGDHRSMPromotionReceipt"
    s3FailClosedGuard
    finiteCategoricalReceiptPromoted
    ( "finite p2/p3/p5 receipt coverage may be cited"
    ∷ "full DHR/DR, exact SM match, and physical sector promotion remain false"
    ∷ []
    )
  ∷ mkLaneObject
    "chemistry, DNA, and supervoxel"
    chemistryLane
    "local definitional chemistry and DNA quotient surfaces"
    "DASHI.Constants.Registry"
    "canonicalChemistryKnownInputsReferenceReceipt"
    s3FailClosedGuard
    localDefinitionalReceiptPromoted
    ( "localDefinitionalChemistryPopulated=true"
    ∷ "physical chemistry, spectroscopy, bonding, and wet-lab validation remain false"
    ∷ []
    )
  ∷ mkLaneObject
    "biology, genome, and brain"
    biologyDNABrainLane
    "observation, sequence, cell, connectome, and clinical boundaries"
    "DASHI.Interop.PhysicsChemistryBiologyDNAUnificationDischarge"
    "aggregate biology/DNA non-promotion receipts"
    s3FailClosedGuard
    typedSurfaceOnlyPromoted
    ( "structured bridge and observation surfaces are present"
    ∷ "causation, intervention, clinical validity, and genome-to-connectome closure remain false"
    ∷ []
    )
  ∷ mkLaneObject
    "Maxwell and gauge"
    maxwellGaugeLane
    "curvature, Hodge, source-current, and unit-calibration target"
    "DASHI.Constants.Registry"
    "Maxwell known-law slot"
    s1BoundedObservable
    conditionalOnExternalAuthority
    ( "Maxwell target vocabulary and exact c/e references are populated"
    ∷ "field-equation recovery requires metric, source, and calibration adapters"
    ∷ []
    )
  ∷ mkLaneObject
    "GR and weak-field gravity"
    grLane
    "Einstein equation and weak-field/newtonian target vocabulary"
    "DASHI.Constants.Registry"
    "Einstein field equation known-law slot"
    s1BoundedObservable
    conditionalOnExternalAuthority
    ( "c exact and G authority slot are populated"
    ∷ "non-flat curvature, stress-energy, and G calibration remain blockers"
    ∷ []
    )
  ∷ mkLaneObject
    "empirical providers and prediction"
    empiricalLane
    "source/projection/comparison/provenance receipt stack"
    "DASHI.Constants.Registry"
    "canonicalKnownInputsPopulationReceipt"
    s3FailClosedGuard
    externalAuthoritySlotPromoted
    ( "provider and authority slots are named"
    ∷ "accepted authority tokens and empirical adequacy remain false"
    ∷ []
    )
  ∷ mkLaneObject
    "runtime, PNF, and ITIR"
    runtimePNFLane
    "parser, residual, replay, and runtime provenance"
    "DASHI.Constants.Registry"
    "runtime receipt authority slot"
    s3FailClosedGuard
    typedSurfaceOnlyPromoted
    ( "runtime receipt discipline is populated"
    ∷ "semantic truth and replay authority remain external"
    ∷ []
    )
  ∷ mkLaneObject
    "Gate 3 arithmetic and moonshine"
    gate3ArithmeticLane
    "finite norm, density, Mosco, and no-pollution route inputs"
    "DASHI.Physics.Closure.Gate3NormDictionary"
    "Gate3 route receipt family"
    s2FormalReceipt
    routeEvidenceOnlyPromoted
    ( "finite density/fill-distance/norm evidence may be cited as route input"
    ∷ "Gate 3 closure, Mosco recovery, and mass-shell transfer remain open"
    ∷ []
    )
  ∷ mkLaneObject
    "Navier-Stokes Clay-facing route"
    navierStokesLane
    "standard PDE law target plus pressure/phase blockers"
    "DASHI.Physics.Closure.NSPhasePressureGate3Receipt"
    "NS phase/pressure Gate 3 receipt family"
    s3FailClosedGuard
    routeEvidenceOnlyPromoted
    ( "Navier-Stokes law target and obstruction bookkeeping may be cited"
    ∷ "Clay regularity, standard PDE closure, and terminal promotion remain false"
    ∷ []
    )
  ∷ mkLaneObject
    "Yang-Mills Clay-facing route"
    yangMillsLane
    "continuum gauge/QFT law target plus mass-gap blockers"
    "DASHI.Physics.Closure.YMKPActivityRatioMarginReceipt"
    "YM KP/Balaban/OS/Wightman receipt family"
    s3FailClosedGuard
    routeEvidenceOnlyPromoted
    ( "Yang-Mills law target and route evidence may be cited"
    ∷ "continuum YM, mass gap, Wightman reconstruction, and Clay promotion remain false"
    ∷ []
    )
  ∷ []

canonicalLaneMorphisms : List LaneMorphismSlot
canonicalLaneMorphisms =
  mkMorphism
    "exact constants feed quantum references"
    "constants and SI metrology"
    "Schrodinger and quantum measurement"
    consumes
    "canonicalQuantumKnownInputsReferenceReceipt"
    ( "Hilbert representation"
    ∷ "self-adjoint Hamiltonian"
    ∷ "Born probability semantics"
    ∷ []
    )
  ∷ mkMorphism
    "exact constants feed chemistry references"
    "constants and SI metrology"
    "chemistry, DNA, and supervoxel"
    consumes
    "canonicalChemistryKnownInputsReferenceReceipt"
    ( "physical scale-setting"
    ∷ "spectral observable map"
    ∷ "wet-lab provenance"
    ∷ []
    )
  ∷ mkMorphism
    "measured constants feed Standard Model calibration"
    "constants and SI metrology"
    "QFT, DHR, and Standard Model sector"
    externalAuthorityRequired
    "CODATA/PDG measured authority slots"
    ( "particle masses"
    ∷ "couplings"
    ∷ "CKM/PMNS convention"
    ∷ []
    )
  ∷ mkMorphism
    "Maxwell target consumes electromagnetic constants"
    "constants and SI metrology"
    "Maxwell and gauge"
    externalAuthorityRequired
    "Maxwell known-law slot"
    ( "metric/Hodge adapter"
    ∷ "source-current extraction"
    ∷ "epsilon_0/mu_0 authority"
    ∷ []
    )
  ∷ mkMorphism
    "GR target consumes c and G authority"
    "constants and SI metrology"
    "GR and weak-field gravity"
    externalAuthorityRequired
    "Einstein field equation known-law slot"
    ( "G authority"
    ∷ "stress-energy adapter"
    ∷ "non-flat curvature contraction"
    ∷ []
    )
  ∷ mkMorphism
    "chemistry constrains biology inputs"
    "chemistry, DNA, and supervoxel"
    "biology, genome, and brain"
    cites
    "ProteinHormoneChemistryCellBridge and DNA supervoxel surfaces"
    ( "assay authority"
    ∷ "organism/cell-line provenance"
    ∷ "causal intervention receipt"
    ∷ []
    )
  ∷ mkMorphism
    "genome constrains connectome targets"
    "biology, genome, and brain"
    "biology, genome, and brain"
    cites
    "GenomeSensorimotorConnectomeBridge"
    ( "genome dataset receipt"
    ∷ "developmental dynamics calibration"
    ∷ "connectome authority checksum"
    ∷ []
    )
  ∷ mkMorphism
    "quantum surfaces feed QFT targets"
    "Schrodinger and quantum measurement"
    "QFT, DHR, and Standard Model sector"
    blocks
    "AQFT/DHR/GNS adapter family"
    ( "GNS/vacuum state"
    ∷ "local observable net"
    ∷ "DHR/DR authority"
    ∷ []
    )
  ∷ mkMorphism
    "finite categorical receipts feed SM candidates"
    "QFT, DHR, and Standard Model sector"
    "QFT, DHR, and Standard Model sector"
    cites
    "finite prime-lane DHR/SM ledger"
    ( "continuous SU3/SU2/U1 adapters"
    ∷ "exact SM carrier-functor match"
    ∷ "physical CKM/Higgs/lepton authority"
    ∷ []
    )
  ∷ mkMorphism
    "Gate 3 route evidence feeds NS blockers"
    "Gate 3 arithmetic and moonshine"
    "Navier-Stokes Clay-facing route"
    cites
    "Gate3 norm/density/Mosco receipt family"
    ( "nonlinear term passage"
    ∷ "pressure reconstruction"
    ∷ "standard PDE regularity closure"
    ∷ []
    )
  ∷ mkMorphism
    "Gate 3 route evidence feeds YM blockers"
    "Gate 3 arithmetic and moonshine"
    "Yang-Mills Clay-facing route"
    cites
    "Gate3 norm/density/Mosco receipt family"
    ( "OS positivity"
    ∷ "continuum RG convergence"
    ∷ "mass-gap transfer"
    ∷ []
    )
  ∷ mkMorphism
    "empirical authority feeds physics predictions"
    "empirical providers and prediction"
    "Maxwell and gauge"
    validates
    "provider/source/projection/comparison receipt family"
    ( "source checksum"
    ∷ "covariance/comparison law"
    ∷ "accepted authority token"
    ∷ []
    )
  ∷ mkMorphism
    "runtime receipts feed empirical replay"
    "runtime, PNF, and ITIR"
    "empirical providers and prediction"
    validates
    "PNF/ITIR runtime receipt authority"
    ( "parser version"
    ∷ "source checksum"
    ∷ "replayable execution receipt"
    ∷ []
    )
  ∷ mkMorphism
    "Navier-Stokes target translates to standard PDE"
    "Navier-Stokes Clay-facing route"
    "Navier-Stokes Clay-facing route"
    blocks
    "Clay NS proof roadmap"
    ( "weak/strong solution class"
    ∷ "energy inequality"
    ∷ "regularity criterion"
    ∷ []
    )
  ∷ mkMorphism
    "Yang-Mills target translates to standard QFT"
    "Yang-Mills Clay-facing route"
    "Yang-Mills Clay-facing route"
    blocks
    "Clay YM KP/Balaban/OS/Wightman route"
    ( "Lie algebra representation"
    ∷ "OS positivity"
    ∷ "Wightman reconstruction"
    ∷ "continuum mass shell"
    ∷ []
    )
  ∷ mkMorphism
    "authority sources bind measured constants"
    "constants and SI metrology"
    "empirical providers and prediction"
    externalAuthorityRequired
    "AuthoritySourceSlot appliesTo map"
    ( "authorityVersion"
    ∷ "sourceChecksum"
    ∷ "valueUncertainty"
    ∷ "roundingPolicy"
    ∷ []
    )
  ∷ []

canonicalRegistryLaneBindings : List RegistryLaneBinding
canonicalRegistryLaneBindings =
  mkRegistryBinding
    "SI defining constants"
    "exactSIDefiningConstants"
    "constants and SI metrology"
    "canonicalKnownInputsPopulationReceipt"
    exactReferenceInputPromoted
    ( "may be cited as exact reference inputs"
    ∷ "do not derive laws or calibration"
    ∷ []
    )
  ∷ mkRegistryBinding
    "SI derived expressions"
    "exactSIDerivedConstants"
    "quantum, chemistry, metrology, and simulator lanes"
    "canonicalKnownInputsPopulationReceipt"
    exactReferenceInputPromoted
    ( "expression exactness only"
    ∷ "rounding policy required at numeric use site"
    ∷ []
    )
  ∷ mkRegistryBinding
    "CODATA measured constants"
    "measuredPhysicsConstantSlots"
    "physics and chemistry adapters"
    "canonicalKnownInputsPopulationReceipt"
    externalAuthoritySlotPromoted
    ( "source/version/unit/uncertainty required"
    ∷ "numeric value not frozen by this registry"
    ∷ []
    )
  ∷ mkRegistryBinding
    "PDG particle data placeholders"
    "measuredPhysicsConstantSlots"
    "QFT and Standard Model sector"
    "canonicalKnownInputsPopulationReceipt"
    externalAuthoritySlotPromoted
    ( "PDG/provider authority required"
    ∷ "scheme and convention required"
    ∷ []
    )
  ∷ mkRegistryBinding
    "NIST Chemistry WebBook and domain chemistry sources"
    "authoritySourceSlots"
    "chemistry, DNA, and supervoxel"
    "canonicalChemistryKnownInputsReferenceReceipt"
    externalAuthoritySlotPromoted
    ( "property checksum"
    ∷ "temperature/activity convention"
    ∷ "wet-lab/provider provenance"
    ∷ []
    )
  ∷ mkRegistryBinding
    "physics law targets"
    "physicsLawSlots"
    "Maxwell, Schrodinger, GR, SM, NS, and YM"
    "canonicalKnownInputsPopulationReceipt"
    typedSurfaceOnlyPromoted
    ( "standard law vocabulary only"
    ∷ "lane adapters and validation remain required"
    ∷ []
    )
  ∷ mkRegistryBinding
    "chemistry law targets"
    "chemistryLawSlots"
    "chemistry and biology adapters"
    "canonicalChemistryKnownInputsReferenceReceipt"
    localDefinitionalReceiptPromoted
    ( "local definitional population only"
    ∷ "physical chemistry and wet-lab validation remain false"
    ∷ []
    )
  ∷ mkRegistryBinding
    "biology law targets"
    "biologyLawSlots"
    "biology, DNA, brain, and clinical lanes"
    "canonicalKnownInputsPopulationReceipt"
    typedSurfaceOnlyPromoted
    ( "model-law targets only"
    ∷ "causation, intervention, clinical validity, and external validation remain blocked"
    ∷ []
    )
  ∷ mkRegistryBinding
    "empirical runtime laws"
    "empiricalRuntimeLawSlots"
    "empirical and runtime lanes"
    "canonicalKnownInputsPopulationReceipt"
    typedSurfaceOnlyPromoted
    ( "provenance/checksum/replay discipline only"
    ∷ "semantic truth and empirical adequacy remain false"
    ∷ []
    )
  ∷ mkRegistryBinding
    "BIPM and NIST SI authority"
    "authoritySourceSlots"
    "constants and SI metrology"
    "canonicalKnownInputsPopulationReceipt"
    externalAuthoritySlotPromoted
    ( "source class and URI populated"
    ∷ "accepted authority token still lane-specific"
    ∷ []
    )
  ∷ mkRegistryBinding
    "HEPData/provider empirical authority"
    "authoritySourceSlots"
    "empirical providers and prediction"
    "canonicalKnownInputsPopulationReceipt"
    externalAuthoritySlotPromoted
    ( "provider receipt required"
    ∷ "comparison law and covariance required"
    ∷ []
    )
  ∷ mkRegistryBinding
    "PNF/ITIR runtime authority"
    "authoritySourceSlots"
    "runtime, PNF, and ITIR"
    "canonicalKnownInputsPopulationReceipt"
    typedSurfaceOnlyPromoted
    ( "runtime provenance only"
    ∷ "truth by parser output remains blocked"
    ∷ []
    )
  ∷ mkRegistryBinding
    "NS and YM Clay law targets"
    "physicsLawSlots"
    "Navier-Stokes and Yang-Mills"
    "canonicalKnownInputsPopulationReceipt"
    routeEvidenceOnlyPromoted
    ( "law target/source vocabulary only"
    ∷ "Clay promotion remains false"
    ∷ []
    )
  ∷ mkRegistryBinding
    "Gate 3 route receipts"
    "route receipt family"
    "Gate 3 arithmetic and moonshine"
    "Gate3 norm/density/Mosco receipt family"
    routeEvidenceOnlyPromoted
    ( "finite route evidence only"
    ∷ "Gate 3 closure and continuum transfer remain open"
    ∷ []
    )
  ∷ []

record CategoricalInterlinkReceipt : Set₁ where
  field
    sourcePopulationReceipt :
      Registry.KnownInputsPopulationReceipt

    sourceAuthorityPolicyReceipt :
      Registry.AuthorityConsumptionPolicyReceipt

    sourcePhysicsAdapterReceipt :
      Registry.PhysicsAdapterKnownInputsReferenceReceipt

    sourceArithmeticGate3Receipt :
      Registry.ArithmeticGate3KnownInputsReferenceReceipt

    sourceQuantumReceipt :
      Registry.QuantumKnownInputsReferenceReceipt

    sourceChemistryReceipt :
      Registry.ChemistryKnownInputsReferenceReceipt

    sourceBiologyReceipt :
      Registry.BiologyKnownInputsReferenceReceipt

    sourceEmpiricalRuntimeReceipt :
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt

    promotionLadder :
      List PromotionLadderRow

    laneObjects :
      List LaneObjectSlot

    laneMorphisms :
      List LaneMorphismSlot

    registryBindings :
      List RegistryLaneBinding

    promotionLadderCount :
      Nat

    promotionLadderCountMatches :
      promotionLadderCount ≡ listCount promotionLadder

    laneObjectCount :
      Nat

    laneObjectCountMatches :
      laneObjectCount ≡ listCount laneObjects

    laneMorphismCount :
      Nat

    laneMorphismCountMatches :
      laneMorphismCount ≡ listCount laneMorphisms

    registryBindingCount :
      Nat

    registryBindingCountMatches :
      registryBindingCount ≡ listCount registryBindings

    categoricalGraphOnly :
      Bool

    categoricalGraphOnlyIsTrue :
      categoricalGraphOnly ≡ true

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    empiricalAdequacyAccepted :
      Bool

    empiricalAdequacyAcceptedIsFalse :
      empiricalAdequacyAccepted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    fullStandardModelPromoted :
      Bool

    fullStandardModelPromotedIsFalse :
      fullStandardModelPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

open CategoricalInterlinkReceipt public

canonicalCategoricalInterlinkReceipt : CategoricalInterlinkReceipt
canonicalCategoricalInterlinkReceipt = record
  { sourcePopulationReceipt =
      Registry.canonicalKnownInputsPopulationReceipt
  ; sourceAuthorityPolicyReceipt =
      Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; sourcePhysicsAdapterReceipt =
      Registry.canonicalPhysicsAdapterKnownInputsReferenceReceipt
  ; sourceArithmeticGate3Receipt =
      Registry.canonicalArithmeticGate3KnownInputsReferenceReceipt
  ; sourceQuantumReceipt =
      Registry.canonicalQuantumKnownInputsReferenceReceipt
  ; sourceChemistryReceipt =
      Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; sourceBiologyReceipt =
      Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; sourceEmpiricalRuntimeReceipt =
      Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; promotionLadder = canonicalPromotionLadder
  ; laneObjects = canonicalLaneObjects
  ; laneMorphisms = canonicalLaneMorphisms
  ; registryBindings = canonicalRegistryLaneBindings
  ; promotionLadderCount = listCount canonicalPromotionLadder
  ; promotionLadderCountMatches = refl
  ; laneObjectCount = listCount canonicalLaneObjects
  ; laneObjectCountMatches = refl
  ; laneMorphismCount = listCount canonicalLaneMorphisms
  ; laneMorphismCountMatches = refl
  ; registryBindingCount = listCount canonicalRegistryLaneBindings
  ; registryBindingCountMatches = refl
  ; categoricalGraphOnly = true
  ; categoricalGraphOnlyIsTrue = refl
  ; theoremPromoted = false
  ; theoremPromotedIsFalse = refl
  ; empiricalAdequacyAccepted = false
  ; empiricalAdequacyAcceptedIsFalse = refl
  ; clayPromoted = false
  ; clayPromotedIsFalse = refl
  ; fullStandardModelPromoted = false
  ; fullStandardModelPromotedIsFalse = refl
  ; terminalPromotion = false
  ; terminalPromotionIsFalse = refl
  }

canonicalPromotionLadderCountIs7 :
  listCount (promotionLadder canonicalCategoricalInterlinkReceipt) ≡ 7
canonicalPromotionLadderCountIs7 = refl

canonicalLaneObjectCountIs12 :
  listCount (laneObjects canonicalCategoricalInterlinkReceipt) ≡ 12
canonicalLaneObjectCountIs12 = refl

canonicalLaneMorphismCountIs16 :
  listCount (laneMorphisms canonicalCategoricalInterlinkReceipt) ≡ 16
canonicalLaneMorphismCountIs16 = refl

canonicalRegistryBindingCountIs14 :
  listCount (registryBindings canonicalCategoricalInterlinkReceipt) ≡ 14
canonicalRegistryBindingCountIs14 = refl

categoricalInterlinkKeepsTheoremPromotionFalse :
  theoremPromoted canonicalCategoricalInterlinkReceipt ≡ false
categoricalInterlinkKeepsTheoremPromotionFalse = refl

categoricalInterlinkKeepsClayPromotionFalse :
  clayPromoted canonicalCategoricalInterlinkReceipt ≡ false
categoricalInterlinkKeepsClayPromotionFalse = refl

categoricalInterlinkKeepsTerminalPromotionFalse :
  terminalPromotion canonicalCategoricalInterlinkReceipt ≡ false
categoricalInterlinkKeepsTerminalPromotionFalse = refl
