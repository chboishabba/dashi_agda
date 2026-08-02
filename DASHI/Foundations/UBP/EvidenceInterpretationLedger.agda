module DASHI.Foundations.UBP.EvidenceInterpretationLedger where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.HiddenLiftProjectionCore as HiddenLift
import DASHI.Core.SourceProcessEvidenceCore as SourceEvidence

------------------------------------------------------------------------
-- Evidence-status vocabulary.
--
-- The ledger distinguishes mathematical provenance, implementation evidence,
-- internal derivation, empirical comparison, prediction, interpretation, and
-- unresolved formal gaps.  Moving between statuses requires a separate bridge;
-- no row promotes scientific, empirical, metaphysical, or theorem authority.

data ClaimStatus : Set where
  standardTheorem :
    ClaimStatus

  implementationVerified :
    ClaimStatus

  ubpDefinition :
    ClaimStatus

  derivedInternalTheorem :
    ClaimStatus

  empiricalFit :
    ClaimStatus

  outOfSamplePrediction :
    ClaimStatus

  interpretiveConjecture :
    ClaimStatus

  formalGap :
    ClaimStatus

data ValidationLevel : Set where
  bibliographicProvenanceOnly :
    ValidationLevel

  unitTested :
    ValidationLevel

  exhaustivelyEnumeratedFiniteDomain :
    ValidationLevel

  internallyDerived :
    ValidationLevel

  crossImplemented :
    ValidationLevel

  proofAssistantChecked :
    ValidationLevel

  retrospectivelyComparedWithData :
    ValidationLevel

  preregisteredHeldOutTest :
    ValidationLevel

  independentlyReplicated :
    ValidationLevel

  unresolvedValidation :
    ValidationLevel

record ClaimRow : Set where
  constructor claimRow
  field
    claimLabel :
      String

    claimStatus :
      ClaimStatus

    validationLevel :
      ValidationLevel

    sourceOrDefinitionReading :
      String

    validationReading :
      String

    remainingGap :
      String

    promotesScientificAuthority :
      Bool

    promotesScientificAuthorityIsFalse :
      promotesScientificAuthority ≡ false

    promotesEmpiricalAuthority :
      Bool

    promotesEmpiricalAuthorityIsFalse :
      promotesEmpiricalAuthority ≡ false

    promotesMetaphysicalAuthority :
      Bool

    promotesMetaphysicalAuthorityIsFalse :
      promotesMetaphysicalAuthority ≡ false

    promotesTheoremAuthority :
      Bool

    promotesTheoremAuthorityIsFalse :
      promotesTheoremAuthority ≡ false

open ClaimRow public

mkNonPromotingClaimRow :
  String →
  ClaimStatus →
  ValidationLevel →
  String →
  String →
  String →
  ClaimRow
mkNonPromotingClaimRow label status level source validation gap =
  claimRow
    label
    status
    level
    source
    validation
    gap
    false
    refl
    false
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Canonical eight-way UBP ledger.

standardGolayLeechRow :
  ClaimRow
standardGolayLeechRow =
  mkNonPromotingClaimRow
    "standard Golay Hexacode MOG and Leech mathematics"
    standardTheorem
    bibliographicProvenanceOnly
    "established external mathematics is attributed in DASHI.Foundations.UBP.SourceAtlas"
    "bibliographic attribution is not a proof import; concrete DASHI theorem instances require local constructions or accepted external theorem adapters"
    "formalisation of the selected standard constructions and invariant statements remains distinct from their citation"

finiteEnumerationRow :
  ClaimRow
finiteEnumerationRow =
  mkNonPromotingClaimRow
    "finite implementation checks"
    implementationVerified
    exhaustivelyEnumeratedFiniteDomain
    "the supplied UBP repository reports finite codeword, octad, minimal-vector, Gray-pair, and cascade checks"
    "a finite exhaustive program can verify its represented finite domain relative to its implementation and specification"
    "independent implementation, proof-assistant correspondence, and source-to-specification agreement are separate obligations"

ubpDefinitionRow :
  ClaimRow
ubpDefinitionRow =
  mkNonPromotingClaimRow
    "TAX NRCI TGIC and coherence-threshold definitions"
    ubpDefinition
    internallyDerived
    "the model declares observables and thresholds including TAX, NRCI, TGIC scores, and the NRCI one-half horizon"
    "well-typed evaluation establishes a model definition, not an external physical law"
    "scientific meaning requires an explicit calibrated interpretation bridge"

internalPerturbationRow :
  ClaimRow
internalPerturbationRow =
  mkNonPromotingClaimRow
    "activation de-excitation and cascade identities"
    derivedInternalTheorem
    internallyDerived
    "the activation and de-excitation formulas and the minus-three-quarters cancellation follow from the declared additive TAX functional"
    "these are valid internal algebraic consequences when their carrier and constant are fixed"
    "physical cascade, vacuum, manifestation, and force interpretations remain outside the derivation"

empiricalFitRow :
  ClaimRow
empiricalFitRow =
  mkNonPromotingClaimRow
    "particle chemistry biology and materials comparisons"
    empiricalFit
    retrospectivelyComparedWithData
    "reported numerical agreement with already observed datasets is represented as empirical fit"
    "retrospective agreement alone does not determine search degrees of freedom, multiplicity correction, identifiability, or causal explanation"
    "dataset provenance, formula search space, parameter count, uncertainty, baselines, and held-out evaluation remain required"

predictionRow :
  ClaimRow
predictionRow =
  mkNonPromotingClaimRow
    "fixed future UBP predictions"
    outOfSamplePrediction
    unresolvedValidation
    "a prediction qualifies for this row only when formula, admissible choices, target, uncertainty, and evaluation protocol are frozen before target observation"
    "the ledger records prediction status but supplies no preregistration or experimental result"
    "timestamped preregistration, independent measurement, and a declared success criterion remain required"

interpretiveRow :
  ClaimRow
interpretiveRow =
  mkNonPromotingClaimRow
    "mass vacuum gravity manifestation and semantic interpretations"
    interpretiveConjecture
    unresolvedValidation
    "physical and semantic names are retained as proposed interpretations of model states and observables"
    "terminology and structural analogy do not produce a bridge theorem or scientific authority"
    "calibration, invariance, empirical contact, prediction, and replication receipts remain absent"

formalGapRow :
  ClaimRow
formalGapRow =
  mkNonPromotingClaimRow
    "open UBP bridge obligations"
    formalGap
    unresolvedValidation
    "unresolved obligations include exact-real interval certification, Leech membership, M24-equivariance, semantic metric control, and structural Leech-to-3D projection"
    "the gap row prevents implementation success from being promoted across missing bridges"
    "each obligation requires a separately typed witness before promotion"

canonicalUBPClaimRows :
  List ClaimRow
canonicalUBPClaimRows =
  standardGolayLeechRow
  ∷ finiteEnumerationRow
  ∷ ubpDefinitionRow
  ∷ internalPerturbationRow
  ∷ empiricalFitRow
  ∷ predictionRow
  ∷ interpretiveRow
  ∷ formalGapRow
  ∷ []

claimRowCount :
  List ClaimRow →
  Nat
claimRowCount [] =
  zero
claimRowCount (_ ∷ rows) =
  suc (claimRowCount rows)

canonicalUBPClaimRowCount :
  Nat
canonicalUBPClaimRowCount =
  claimRowCount canonicalUBPClaimRows

canonicalUBPClaimRowCountIsEight :
  canonicalUBPClaimRowCount ≡ 8
canonicalUBPClaimRowCountIsEight =
  refl

data AllClaimRowsNonPromoting :
  List ClaimRow →
  Set where
  allClaimRowsNonPromotingNil :
    AllClaimRowsNonPromoting []

  allClaimRowsNonPromotingCons :
    ∀ {row rows} →
    promotesScientificAuthority row ≡ false →
    promotesEmpiricalAuthority row ≡ false →
    promotesMetaphysicalAuthority row ≡ false →
    promotesTheoremAuthority row ≡ false →
    AllClaimRowsNonPromoting rows →
    AllClaimRowsNonPromoting (row ∷ rows)

proveAllClaimRowsNonPromoting :
  (rows : List ClaimRow) →
  AllClaimRowsNonPromoting rows
proveAllClaimRowsNonPromoting [] =
  allClaimRowsNonPromotingNil
proveAllClaimRowsNonPromoting (row ∷ rows) =
  allClaimRowsNonPromotingCons
    (promotesScientificAuthorityIsFalse row)
    (promotesEmpiricalAuthorityIsFalse row)
    (promotesMetaphysicalAuthorityIsFalse row)
    (promotesTheoremAuthorityIsFalse row)
    (proveAllClaimRowsNonPromoting rows)

canonicalUBPClaimRowsNonPromoting :
  AllClaimRowsNonPromoting canonicalUBPClaimRows
canonicalUBPClaimRowsNonPromoting =
  proveAllClaimRowsNonPromoting canonicalUBPClaimRows

------------------------------------------------------------------------
-- Explicit interpretation bridge.

record InterpretationBridge : Set₁ where
  field
    ModelState :
      Set

    ModelObservable :
      Set

    ExternalTarget :
      Set

    Prediction :
      Set

    interpretState :
      ModelState →
      ExternalTarget

    observeModel :
      ModelState →
      ModelObservable

    predictExternal :
      ModelState →
      Prediction

    calibrationReceipt :
      Set

    invarianceReceipt :
      Set

    uncertaintyReceipt :
      Set

    heldOutProtocolReceipt :
      Set

    externalReplicationReceipt :
      Set

    bridgeReading :
      String

open InterpretationBridge public

record InterpretationBoundaryStatus : Set where
  constructor interpretationBoundaryStatus
  field
    interpretationMapProposed :
      Bool

    interpretationMapProposedIsTrue :
      interpretationMapProposed ≡ true

    calibrationSupplied :
      Bool

    calibrationSuppliedIsFalse :
      calibrationSupplied ≡ false

    invarianceSupplied :
      Bool

    invarianceSuppliedIsFalse :
      invarianceSupplied ≡ false

    heldOutPredictionProtocolSupplied :
      Bool

    heldOutPredictionProtocolSuppliedIsFalse :
      heldOutPredictionProtocolSupplied ≡ false

    externalReplicationSupplied :
      Bool

    externalReplicationSuppliedIsFalse :
      externalReplicationSupplied ≡ false

    physicalAuthorityPromoted :
      Bool

    physicalAuthorityPromotedIsFalse :
      physicalAuthorityPromoted ≡ false

    semanticAuthorityPromoted :
      Bool

    semanticAuthorityPromotedIsFalse :
      semanticAuthorityPromoted ≡ false

    boundaryReading :
      String

open InterpretationBoundaryStatus public

canonicalInterpretationBoundaryStatus :
  InterpretationBoundaryStatus
canonicalInterpretationBoundaryStatus =
  interpretationBoundaryStatus
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "UBP interpretations may be proposed, but calibration, invariance, held-out testing, replication, and authority require an inhabited InterpretationBridge and accepted domain receipts"

------------------------------------------------------------------------
-- Cross-pollination with existing DASHI evidence and projection cores.

UBPFibreRestrictionObligation :
  Set₁
UBPFibreRestrictionObligation =
  Fibre.FibreRestrictionCore

ubpEvidenceAuthorityBundle :
  Authority.AuthorityNonPromotionBundle
ubpEvidenceAuthorityBundle =
  Authority.mkClosedAuthorityNonPromotionBundle
    "UBP evidence and interpretation authority boundary"

ubpSourceProcessEvidenceReceipt :
  SourceEvidence.SourceProcessEvidenceReceipt
    SourceEvidence.canonicalSourceProcessEvidenceSurface
ubpSourceProcessEvidenceReceipt =
  SourceEvidence.canonicalSourceProcessEvidenceReceipt

ubpHiddenLiftProjectionReceipt :
  HiddenLift.HiddenLiftProjectionReceipt
    HiddenLift.canonicalHiddenLiftProjectionSurface
ubpHiddenLiftProjectionReceipt =
  HiddenLift.canonicalHiddenLiftProjectionReceipt

ubpInterpretationGenericReceipt :
  GenericReceipt.GenericReceipt
ubpInterpretationGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "UBP evidence and interpretation ledger"
    "DASHI.Foundations.UBP.EvidenceInterpretationLedger"
    "canonicalUBPClaimRows and canonicalInterpretationBoundaryStatus"
    "eight explicit claim statuses separate standard mathematics, finite implementation evidence, UBP definitions, internal derivations, empirical fits, predictions, interpretations, and formal gaps"
    "no scientific, empirical, metaphysical, semantic, physical, theorem, or external-verification authority is promoted without separately inhabited bridge and authority receipts"
    "agda -i . DASHI/Foundations/UBP/EvidenceInterpretationLedger.agda"

ubpInterpretationGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim ubpInterpretationGenericReceipt ≡ false
ubpInterpretationGenericReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse ubpInterpretationGenericReceipt
