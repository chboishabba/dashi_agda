module DASHI.Promotion.SIMetrologyPayloadDependencyDAG where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- SI metrology dependency DAG.
--
-- This module is a fail-closed inventory surface for the exact SI
-- defining-constant, atomic-clock second, metre, Rydberg/spectroscopy, and
-- W4/Candidate256 calibration chain.  It records dependency nodes, edge
-- labels, gate kinds, strict closure levels, source-module references, and
-- canonical blockers.  It does not construct an authority artifact, parse a
-- live external document, accept an empirical receipt, or promote any row.

data SIMetrologyGateKind : Set where
  internalReflGate :
    SIMetrologyGateKind

  externalAuthorityGate :
    SIMetrologyGateKind

  empiricalReceiptGate :
    SIMetrologyGateKind

  promotionTokenGate :
    SIMetrologyGateKind

data SIMetrologyClosureLevel : Set where
  carrierShapeLevel :
    SIMetrologyClosureLevel

  authorityPayloadLevel :
    SIMetrologyClosureLevel

  siUnitAdapterLevel :
    SIMetrologyClosureLevel

  quantumClockObservableLevel :
    SIMetrologyClosureLevel

  spectroscopyPayloadLevel :
    SIMetrologyClosureLevel

  w4CandidateReceiptLevel :
    SIMetrologyClosureLevel

  terminalPromotionLevel :
    SIMetrologyClosureLevel

data SIMetrologyStrictBefore :
  SIMetrologyClosureLevel →
  SIMetrologyClosureLevel →
  Set where
  carrierBeforeAuthority :
    SIMetrologyStrictBefore carrierShapeLevel authorityPayloadLevel

  authorityBeforeUnitAdapter :
    SIMetrologyStrictBefore authorityPayloadLevel siUnitAdapterLevel

  unitAdapterBeforeQuantumClock :
    SIMetrologyStrictBefore siUnitAdapterLevel quantumClockObservableLevel

  unitAdapterBeforeSpectroscopy :
    SIMetrologyStrictBefore siUnitAdapterLevel spectroscopyPayloadLevel

  quantumClockBeforeW4 :
    SIMetrologyStrictBefore quantumClockObservableLevel w4CandidateReceiptLevel

  spectroscopyBeforeW4 :
    SIMetrologyStrictBefore spectroscopyPayloadLevel w4CandidateReceiptLevel

  w4BeforeTerminal :
    SIMetrologyStrictBefore w4CandidateReceiptLevel terminalPromotionLevel

record SIMetrologyDAGNode : Set where
  field
    nodeName :
      String

    canonicalSurface :
      String

    canonicalSymbol :
      String

    sourceModuleName :
      String

    sourceRefName :
      String

    closureLevel :
      SIMetrologyClosureLevel

    gateKind :
      SIMetrologyGateKind

    internallyDischargeable :
      Bool

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    blockerLabel :
      String

open SIMetrologyDAGNode public

mkNode :
  String →
  String →
  String →
  String →
  String →
  SIMetrologyClosureLevel →
  SIMetrologyGateKind →
  Bool →
  String →
  SIMetrologyDAGNode
mkNode name surface symbol moduleName ref level kind internal blocker =
  record
    { nodeName =
        name
    ; canonicalSurface =
        surface
    ; canonicalSymbol =
        symbol
    ; sourceModuleName =
        moduleName
    ; sourceRefName =
        ref
    ; closureLevel =
        level
    ; gateKind =
        kind
    ; internallyDischargeable =
        internal
    ; promoted =
        false
    ; promotedIsFalse =
        refl
    ; blockerLabel =
        blocker
    }

deltaNuCsCarrierNode : SIMetrologyDAGNode
deltaNuCsCarrierNode =
  mkNode
    "delta-nu-Cs exact integer carrier"
    "SI exact constant parsed carrier request"
    "Delta nu Cs = 9192631770 Hz"
    "DASHI.Promotion.SIExactConstantParsedCarrierRequest"
    "canonicalDeltaNuCsNaturalCarrier"
    carrierShapeLevel
    internalReflGate
    true
    "no authority artifact, SHA-256, access date, or consumer ingestion receipt is accepted here"

cExactCarrierNode : SIMetrologyDAGNode
cExactCarrierNode =
  mkNode
    "speed-of-light exact integer carrier"
    "SI exact constant parsed carrier request"
    "c = 299792458 m s^-1"
    "DASHI.Promotion.SIExactConstantParsedCarrierRequest"
    "canonicalCMetrePerSecondIntegerCarrier"
    carrierShapeLevel
    internalReflGate
    true
    "exact carrier exists, but the BIPM authority payload remains unaccepted"

hExactCarrierNode : SIMetrologyDAGNode
hExactCarrierNode =
  mkNode
    "Planck constant exact scientific-decimal carrier"
    "SI exact constant parsed carrier request"
    "h = 6.62607015e-34 J s"
    "DASHI.Promotion.SIExactConstantParsedCarrierRequest"
    "canonicalHScientificDecimalCarrier"
    carrierShapeLevel
    internalReflGate
    true
    "hbar and Stone lanes still require accepted h authority payload and dimensional ingestion"

siAuthorityPayloadNode : SIMetrologyDAGNode
siAuthorityPayloadNode =
  mkNode
    "BIPM SI defining-constant authority payload"
    "external authority artifact row"
    "BIPM SI defining constants"
    "DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest"
    "SIDefiningConstantAuthorityArtifactRowRequest"
    authorityPayloadLevel
    externalAuthorityGate
    false
    "document identity, SHA-256 digest, access date, raw numeric text, raw uncertainty text, parsed carrier, independence receipt, and consumer ingestion receipt are missing"

cs133SecondNode : SIMetrologyDAGNode
cs133SecondNode =
  mkNode
    "Cs-133 SI second calibration route"
    "atomic-clock second carrier"
    "1 s = 9192631770 Cs-133 periods"
    "DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge"
    "canonicalCs133SISecondAnchor"
    siUnitAdapterLevel
    internalReflGate
    true
    "unit carrier and dimension route are structural only until the SI authority token is accepted"

metreFromSecondAndCNode : SIMetrologyDAGNode
metreFromSecondAndCNode =
  mkNode
    "metre from SI second and exact c"
    "metre adapter"
    "1 m = c * 1 s / 299792458"
    "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
    "canonicalSIMetreFromSecondAndCAdapter"
    siUnitAdapterLevel
    internalReflGate
    true
    "derived metre carrier exists as dimension route only; authorityPayloadPromoted remains false"

hbarStoneTopologyNode : SIMetrologyDAGNode
hbarStoneTopologyNode =
  mkNode
    "SI second real-time Stone topology request"
    "Stone/Hilbert time-parameter request"
    "U(t) = exp(-i H t / hbar)"
    "DASHI.Physics.Closure.AtomicClockSecondRealTimeTopologyRequest"
    "canonicalAtomicClockSecondRealTimeTopologyRequest"
    quantumClockObservableLevel
    externalAuthorityGate
    false
    "constructive real-time carrier, dense self-adjoint domain, hbar payload, and Stone theorem authority remain open"

dimensionlessClockObservableNode : SIMetrologyDAGNode
dimensionlessClockObservableNode =
  mkNode
    "dimensionless quantum-clock observables"
    "clock phase and redshift dimension-cancellation surface"
    "omega0 * deltaTau and DeltaU / c^2 are dimensionless"
    "DASHI.Physics.Closure.QuantumClockDimensionlessObservableLaw"
    "canonicalQuantumClockDimensionlessObservableLaw"
    quantumClockObservableLevel
    empiricalReceiptGate
    true
    "dimension arithmetic closes internally, but numeric clock payload and empirical redshift receipt remain missing"

rydbergWavenumberNode : SIMetrologyDAGNode
rydbergWavenumberNode =
  mkNode
    "Rydberg wavenumber spectroscopy payload"
    "metre-to-wavenumber spectroscopy adapter"
    "dim R_infinity = m^-1"
    "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
    "RydbergWavenumberDimensionAdapter"
    spectroscopyPayloadLevel
    externalAuthorityGate
    false
    "CODATA R_infinity payload, reduced-mass constants, and NIST ASD spectral-line receipt remain external"

w4ChecklistNode : SIMetrologyDAGNode
w4ChecklistNode =
  mkNode
    "W4 atomic-clock Candidate256 receipt checklist"
    "Candidate256 physical calibration receipt checklist"
    "Candidate256PhysicalCalibrationExternalReceipt field map"
    "DASHI.Physics.Closure.W4AtomicClockCandidateReceiptChecklist"
    "canonicalAtomicClockCandidateReceiptChecklist"
    w4CandidateReceiptLevel
    externalAuthorityGate
    false
    "Candidate256PhysicalCalibrationAuthorityToken has no inhabitant"

terminalPromotionNode : SIMetrologyDAGNode
terminalPromotionNode =
  mkNode
    "SI metrology terminal promotion token"
    "terminal guard"
    "SI/atomic-clock/metre/Rydberg/W4 promotion"
    "DASHI.Promotion.SIMetrologyPayloadDependencyDAG"
    "canonicalSIMetrologyPayloadDependencyDAG"
    terminalPromotionLevel
    promotionTokenGate
    false
    "terminal promotion requires all authority, empirical, spectroscopy, and W4 receipt gates"

canonicalSIMetrologyDAGNodes : List SIMetrologyDAGNode
canonicalSIMetrologyDAGNodes =
  deltaNuCsCarrierNode
  ∷ cExactCarrierNode
  ∷ hExactCarrierNode
  ∷ siAuthorityPayloadNode
  ∷ cs133SecondNode
  ∷ metreFromSecondAndCNode
  ∷ hbarStoneTopologyNode
  ∷ dimensionlessClockObservableNode
  ∷ rydbergWavenumberNode
  ∷ w4ChecklistNode
  ∷ terminalPromotionNode
  ∷ []

record SIMetrologyDAGEdge
  (sourceLevel targetLevel : SIMetrologyClosureLevel) : Set where
  field
    edgeName :
      String

    sourceNodeName :
      String

    targetNodeName :
      String

    sourceModuleName :
      String

    targetModuleName :
      String

    dependencyStatement :
      String

    gateKind :
      SIMetrologyGateKind

    strictClosureOrder :
      SIMetrologyStrictBefore sourceLevel targetLevel

    edgeCurrentlyClosed :
      Bool

    edgeCurrentlyClosedIsFalse :
      edgeCurrentlyClosed ≡ false

open SIMetrologyDAGEdge public

mkEdge :
  {sourceLevel targetLevel : SIMetrologyClosureLevel} →
  String →
  String →
  String →
  String →
  String →
  String →
  SIMetrologyGateKind →
  SIMetrologyStrictBefore sourceLevel targetLevel →
  SIMetrologyDAGEdge sourceLevel targetLevel
mkEdge name source target sourceModule targetModule statement kind order =
  record
    { edgeName =
        name
    ; sourceNodeName =
        source
    ; targetNodeName =
        target
    ; sourceModuleName =
        sourceModule
    ; targetModuleName =
        targetModule
    ; dependencyStatement =
        statement
    ; gateKind =
        kind
    ; strictClosureOrder =
        order
    ; edgeCurrentlyClosed =
        false
    ; edgeCurrentlyClosedIsFalse =
        refl
    }

parsedCarriersToAuthorityEdge :
  SIMetrologyDAGEdge carrierShapeLevel authorityPayloadLevel
parsedCarriersToAuthorityEdge =
  mkEdge
    "parsed exact carriers require authority artifact"
    "delta-nu-Cs / c / h exact carrier nodes"
    "BIPM SI defining-constant authority payload"
    "DASHI.Promotion.SIExactConstantParsedCarrierRequest"
    "DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest"
    "internal Nat/decimal carriers must be matched to external BIPM raw text, checksum, access date, independence, and ingestion receipts"
    externalAuthorityGate
    carrierBeforeAuthority

authorityToSIUnitAdapterEdge :
  SIMetrologyDAGEdge authorityPayloadLevel siUnitAdapterLevel
authorityToSIUnitAdapterEdge =
  mkEdge
    "authority payload enables SI second and metre adapters"
    "BIPM SI defining-constant authority payload"
    "Cs-133 second and metre-from-c unit adapters"
    "DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest"
    "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
    "Delta nu Cs supplies the second route; c supplies the derived metre route; both remain fail-closed without accepted authority"
    externalAuthorityGate
    authorityBeforeUnitAdapter

unitAdapterToQuantumClockEdge :
  SIMetrologyDAGEdge siUnitAdapterLevel quantumClockObservableLevel
unitAdapterToQuantumClockEdge =
  mkEdge
    "SI unit adapters feed clock phase and Stone time"
    "SI second / metre / hbar dimensional inputs"
    "quantum-clock observable and real-time topology requests"
    "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
    "DASHI.Physics.Closure.QuantumClockDimensionlessObservableLaw"
    "omega0 * deltaTau is dimensionless and H t / hbar is dimensionless only after time, c, and hbar payloads are present"
    empiricalReceiptGate
    unitAdapterBeforeQuantumClock

unitAdapterToSpectroscopyEdge :
  SIMetrologyDAGEdge siUnitAdapterLevel spectroscopyPayloadLevel
unitAdapterToSpectroscopyEdge =
  mkEdge
    "derived metre feeds Rydberg wavenumber lane"
    "metre from SI second and c"
    "Rydberg wavenumber spectroscopy payload"
    "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
    "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
    "m^-1 dimension is available internally; CODATA R_infinity and NIST ASD evidence remain external"
    externalAuthorityGate
    unitAdapterBeforeSpectroscopy

quantumClockToW4Edge :
  SIMetrologyDAGEdge quantumClockObservableLevel w4CandidateReceiptLevel
quantumClockToW4Edge =
  mkEdge
    "clock observables feed W4 empirical calibration receipt"
    "dimensionless clock observables"
    "W4 atomic-clock Candidate256 receipt checklist"
    "DASHI.Physics.Closure.QuantumClockDimensionlessObservableLaw"
    "DASHI.Physics.Closure.W4AtomicClockCandidateReceiptChecklist"
    "W4 cannot promote clock calibration from dimensional laws alone; it requires numeric payload and empirical redshift receipt"
    empiricalReceiptGate
    quantumClockBeforeW4

spectroscopyToW4Edge :
  SIMetrologyDAGEdge spectroscopyPayloadLevel w4CandidateReceiptLevel
spectroscopyToW4Edge =
  mkEdge
    "spectroscopy authority feeds W4 physical calibration context"
    "Rydberg wavenumber spectroscopy payload"
    "W4 atomic-clock Candidate256 receipt checklist"
    "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
    "DASHI.Physics.Closure.W4AtomicClockCandidateReceiptChecklist"
    "Rydberg and NIST ASD rows are empirical authority payloads, not internal dimension lemmas"
    externalAuthorityGate
    spectroscopyBeforeW4

w4ToTerminalPromotionEdge :
  SIMetrologyDAGEdge w4CandidateReceiptLevel terminalPromotionLevel
w4ToTerminalPromotionEdge =
  mkEdge
    "W4 receipt gates terminal SI metrology promotion"
    "W4 atomic-clock Candidate256 receipt checklist"
    "SI metrology terminal promotion token"
    "DASHI.Physics.Closure.W4AtomicClockCandidateReceiptChecklist"
    "DASHI.Promotion.SIMetrologyPayloadDependencyDAG"
    "terminal promotion is blocked until Candidate256PhysicalCalibrationAuthorityToken exists"
    promotionTokenGate
    w4BeforeTerminal

data SIMetrologyAnyDAGEdge : Set where
  carrierAuthorityEdge :
    SIMetrologyDAGEdge carrierShapeLevel authorityPayloadLevel →
    SIMetrologyAnyDAGEdge

  authorityUnitAdapterEdge :
    SIMetrologyDAGEdge authorityPayloadLevel siUnitAdapterLevel →
    SIMetrologyAnyDAGEdge

  unitQuantumClockEdge :
    SIMetrologyDAGEdge siUnitAdapterLevel quantumClockObservableLevel →
    SIMetrologyAnyDAGEdge

  unitSpectroscopyEdge :
    SIMetrologyDAGEdge siUnitAdapterLevel spectroscopyPayloadLevel →
    SIMetrologyAnyDAGEdge

  clockW4Edge :
    SIMetrologyDAGEdge quantumClockObservableLevel w4CandidateReceiptLevel →
    SIMetrologyAnyDAGEdge

  spectroscopyW4Edge :
    SIMetrologyDAGEdge spectroscopyPayloadLevel w4CandidateReceiptLevel →
    SIMetrologyAnyDAGEdge

  w4TerminalEdge :
    SIMetrologyDAGEdge w4CandidateReceiptLevel terminalPromotionLevel →
    SIMetrologyAnyDAGEdge

canonicalSIMetrologyDAGEdges : List SIMetrologyAnyDAGEdge
canonicalSIMetrologyDAGEdges =
  carrierAuthorityEdge parsedCarriersToAuthorityEdge
  ∷ authorityUnitAdapterEdge authorityToSIUnitAdapterEdge
  ∷ unitQuantumClockEdge unitAdapterToQuantumClockEdge
  ∷ unitSpectroscopyEdge unitAdapterToSpectroscopyEdge
  ∷ clockW4Edge quantumClockToW4Edge
  ∷ spectroscopyW4Edge spectroscopyToW4Edge
  ∷ w4TerminalEdge w4ToTerminalPromotionEdge
  ∷ []

record SIMetrologyClosureOrderRow : Set where
  field
    ordinal :
      Nat

    closureLevel :
      SIMetrologyClosureLevel

    levelName :
      String

    requiredBeforeNext :
      String

    canonicalGateKind :
      SIMetrologyGateKind

    rowClosed :
      Bool

    rowClosedIsFalse :
      rowClosed ≡ false

open SIMetrologyClosureOrderRow public

mkOrderRow :
  Nat →
  SIMetrologyClosureLevel →
  String →
  String →
  SIMetrologyGateKind →
  SIMetrologyClosureOrderRow
mkOrderRow n level name required kind =
  record
    { ordinal =
        n
    ; closureLevel =
        level
    ; levelName =
        name
    ; requiredBeforeNext =
        required
    ; canonicalGateKind =
        kind
    ; rowClosed =
        false
    ; rowClosedIsFalse =
        refl
    }

canonicalSIMetrologyClosureOrder : List SIMetrologyClosureOrderRow
canonicalSIMetrologyClosureOrder =
  mkOrderRow
    zero
    carrierShapeLevel
    "internal exact carrier shapes"
    "Delta nu Cs, c, and h Nat/decimal records check by refl but are not authority"
    internalReflGate
  ∷ mkOrderRow
    (suc zero)
    authorityPayloadLevel
    "external authority payload"
    "BIPM/NIST artifact identity, SHA-256, access date, raw text, uncertainty text, parsed carrier, independence, and ingestion receipts"
    externalAuthorityGate
  ∷ mkOrderRow
    (suc (suc zero))
    siUnitAdapterLevel
    "SI second and metre adapters"
    "accepted Delta nu Cs and c payloads must feed the second and metre routes"
    externalAuthorityGate
  ∷ mkOrderRow
    (suc (suc (suc zero)))
    quantumClockObservableLevel
    "clock observable and Stone topology requests"
    "real-time carrier, hbar payload, self-adjoint domain, Stone authority, numeric clock payload, and redshift receipt"
    empiricalReceiptGate
  ∷ mkOrderRow
    (suc (suc (suc (suc zero))))
    spectroscopyPayloadLevel
    "Rydberg and spectral-line payloads"
    "CODATA R_infinity, mass constants, reduced-mass adapter payloads, and NIST ASD spectral-line receipt"
    externalAuthorityGate
  ∷ mkOrderRow
    (suc (suc (suc (suc (suc zero)))))
    w4CandidateReceiptLevel
    "W4 Candidate256 receipt construction"
    "all Candidate256PhysicalCalibrationExternalReceipt fields plus dimensional preservation and factorization witnesses"
    externalAuthorityGate
  ∷ mkOrderRow
    (suc (suc (suc (suc (suc (suc zero))))))
    terminalPromotionLevel
    "terminal SI metrology promotion"
    "single accepted Candidate256PhysicalCalibrationAuthorityToken and observable-promotion token"
    promotionTokenGate
  ∷ []

record SIMetrologyCanonicalBlocker : Set where
  field
    blockerName :
      String

    blockedNode :
      String

    requiredEvidence :
      String

    gateKind :
      SIMetrologyGateKind

    sourceModuleName :
      String

    currentGuardName :
      String

    guardValue :
      Bool

    guardValueIsFalse :
      guardValue ≡ false

open SIMetrologyCanonicalBlocker public

mkBlocker :
  String →
  String →
  String →
  SIMetrologyGateKind →
  String →
  String →
  SIMetrologyCanonicalBlocker
mkBlocker name node evidence kind moduleName guard =
  record
    { blockerName =
        name
    ; blockedNode =
        node
    ; requiredEvidence =
        evidence
    ; gateKind =
        kind
    ; sourceModuleName =
        moduleName
    ; currentGuardName =
        guard
    ; guardValue =
        false
    ; guardValueIsFalse =
        refl
    }

canonicalSIMetrologyBlockers : List SIMetrologyCanonicalBlocker
canonicalSIMetrologyBlockers =
  mkBlocker
    "BIPM/NIST artifact receipt blocker"
    "BIPM SI defining-constant authority payload"
    "document identity, exact SHA-256 digest, access date, and raw UTF-8 text for Delta nu Cs, c, and h"
    externalAuthorityGate
    "DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest"
    "artifactAccepted"
  ∷ mkBlocker
    "parsed-carrier ingestion blocker"
    "SI exact constant parsed carrier manifest"
    "consumer ingestion receipt tying parsed Nat/decimal carriers to accepted authority rows"
    externalAuthorityGate
    "DASHI.Promotion.SIExactConstantParsedCarrierRequest"
    "consumerIngestionReceiptPresent"
  ∷ mkBlocker
    "Stone real-time topology blocker"
    "SI second real-time Stone topology request"
    "constructive RealTimeCarrier, dense HilbertDomain, self-adjoint generator, and Stone theorem authority"
    externalAuthorityGate
    "DASHI.Physics.Closure.AtomicClockSecondRealTimeTopologyRequest"
    "canonicalRequestPromotionAllowedFalse"
  ∷ mkBlocker
    "hbar authority blocker"
    "Stone/Hilbert generator dimensional input"
    "accepted h payload and derived hbar = h / 2 pi receipt"
    externalAuthorityGate
    "DASHI.Promotion.PlanckHbarSIPayloadRequest"
    "hbarAuthorityPayloadSupplied"
  ∷ mkBlocker
    "empirical redshift receipt blocker"
    "dimensionless quantum-clock observable promotion"
    "numeric clock payload and external clock-comparison redshift receipt"
    empiricalReceiptGate
    "DASHI.Physics.Closure.QuantumClockDimensionlessObservableLaw"
    "empiricalReceiptPresent"
  ∷ mkBlocker
    "CODATA R-infinity blocker"
    "Rydberg wavenumber spectroscopy payload"
    "CODATA R_infinity value, uncertainty, covariance/independence, and source artifact"
    externalAuthorityGate
    "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
    "authorityPayloadPromoted"
  ∷ mkBlocker
    "NIST ASD spectral-line blocker"
    "spectroscopy promotion"
    "NIST ASD spectral-line authority token, line URI, checksum, and replay receipt"
    empiricalReceiptGate
    "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
    "spectroscopyPromoted"
  ∷ mkBlocker
    "Candidate256 physical calibration authority token blocker"
    "W4 atomic-clock Candidate256 receipt checklist"
    "accepted Candidate256PhysicalCalibrationAuthorityToken spanning unit carrier, dimension vector, scale maps, factorization, and dimensional preservation"
    promotionTokenGate
    "DASHI.Physics.Closure.W4AtomicClockCandidateReceiptChecklist"
    "rowSatisfied"
  ∷ []

record SIMetrologyPayloadDependencyDAG : Set₁ where
  field
    dagName :
      String

    exactConstantsModuleRef :
      String

    topologyModuleRef :
      String

    dimensionlessObservableModuleRef :
      String

    metreAdapterModuleRef :
      String

    w4ChecklistModuleRef :
      String

    nodes :
      List SIMetrologyDAGNode

    edges :
      List SIMetrologyAnyDAGEdge

    strictClosureOrder :
      List SIMetrologyClosureOrderRow

    canonicalBlockers :
      List SIMetrologyCanonicalBlocker

    terminalPromotionAllowed :
      Bool

    terminalPromotionAllowedIsFalse :
      terminalPromotionAllowed ≡ false

    noAuthorityFabricated :
      Bool

    noAuthorityFabricatedIsTrue :
      noAuthorityFabricated ≡ true

open SIMetrologyPayloadDependencyDAG public

canonicalSIMetrologyPayloadDependencyDAG :
  SIMetrologyPayloadDependencyDAG
canonicalSIMetrologyPayloadDependencyDAG =
  record
    { dagName =
        "SI/atomic-clock/metre/Rydberg/W4 fail-closed dependency DAG"
    ; exactConstantsModuleRef =
        "DASHI.Promotion.SIExactConstantParsedCarrierRequest"
    ; topologyModuleRef =
        "DASHI.Physics.Closure.AtomicClockSecondRealTimeTopologyRequest"
    ; dimensionlessObservableModuleRef =
        "DASHI.Physics.Closure.QuantumClockDimensionlessObservableLaw"
    ; metreAdapterModuleRef =
        "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
    ; w4ChecklistModuleRef =
        "DASHI.Physics.Closure.W4AtomicClockCandidateReceiptChecklist"
    ; nodes =
        canonicalSIMetrologyDAGNodes
    ; edges =
        canonicalSIMetrologyDAGEdges
    ; strictClosureOrder =
        canonicalSIMetrologyClosureOrder
    ; canonicalBlockers =
        canonicalSIMetrologyBlockers
    ; terminalPromotionAllowed =
        false
    ; terminalPromotionAllowedIsFalse =
        refl
    ; noAuthorityFabricated =
        true
    ; noAuthorityFabricatedIsTrue =
        refl
    }

canonicalSIMetrologyTerminalPromotionAllowed :
  terminalPromotionAllowed canonicalSIMetrologyPayloadDependencyDAG ≡ false
canonicalSIMetrologyTerminalPromotionAllowed =
  terminalPromotionAllowedIsFalse canonicalSIMetrologyPayloadDependencyDAG

canonicalSIMetrologyNoAuthorityFabricated :
  noAuthorityFabricated canonicalSIMetrologyPayloadDependencyDAG ≡ true
canonicalSIMetrologyNoAuthorityFabricated =
  noAuthorityFabricatedIsTrue canonicalSIMetrologyPayloadDependencyDAG

canonicalSIMetrologyExactConstantsModuleRef :
  exactConstantsModuleRef canonicalSIMetrologyPayloadDependencyDAG ≡
  "DASHI.Promotion.SIExactConstantParsedCarrierRequest"
canonicalSIMetrologyExactConstantsModuleRef =
  refl

canonicalSIMetrologyTopologyModuleRef :
  topologyModuleRef canonicalSIMetrologyPayloadDependencyDAG ≡
  "DASHI.Physics.Closure.AtomicClockSecondRealTimeTopologyRequest"
canonicalSIMetrologyTopologyModuleRef =
  refl

canonicalSIMetrologyDimensionlessObservableModuleRef :
  dimensionlessObservableModuleRef canonicalSIMetrologyPayloadDependencyDAG ≡
  "DASHI.Physics.Closure.QuantumClockDimensionlessObservableLaw"
canonicalSIMetrologyDimensionlessObservableModuleRef =
  refl

canonicalSIMetrologyMetreAdapterModuleRef :
  metreAdapterModuleRef canonicalSIMetrologyPayloadDependencyDAG ≡
  "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
canonicalSIMetrologyMetreAdapterModuleRef =
  refl

canonicalSIMetrologyW4ChecklistModuleRef :
  w4ChecklistModuleRef canonicalSIMetrologyPayloadDependencyDAG ≡
  "DASHI.Physics.Closure.W4AtomicClockCandidateReceiptChecklist"
canonicalSIMetrologyW4ChecklistModuleRef =
  refl
