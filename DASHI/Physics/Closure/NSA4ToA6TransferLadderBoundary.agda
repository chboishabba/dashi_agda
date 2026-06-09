module DASHI.Physics.Closure.NSA4ToA6TransferLadderBoundary where

-- Fail-closed boundary for the dependency ladder:
--
--   A4 no-angular-collapse/output-support transfer
--     -> A5 kappa-bias vanishing target
--     -> A6 pointwise-to-Abel/leakage identity target
--     -> A7 residual depletion target.
--
-- This module is a ledger only.  It imports the available A4, A5, and A6
-- boundary receipts and records the intended dependency order, blockers,
-- and conditional targets.  It proves no A4, no A5, no A6, no A7, no
-- Navier-Stokes Clay statement, and no terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSA4NoAngularCollapseTransferCompositeBoundary
  as A4
import DASHI.Physics.Closure.NSTransferOperatorBiasNeutralityBoundary
  as A5Bias
import DASHI.Physics.Closure.NSPointwiseToAbelCompositeA6Boundary
  as A6Abel
import DASHI.Physics.Closure.NSA6TheoremLadderBoundary
  as A6Ladder

------------------------------------------------------------------------
-- Local utilities.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

------------------------------------------------------------------------
-- Imported surfaces.

a4NoAngularCollapseTransferCompositeBoundaryReference : String
a4NoAngularCollapseTransferCompositeBoundaryReference =
  "DASHI.Physics.Closure.NSA4NoAngularCollapseTransferCompositeBoundary"

a5TransferOperatorBiasNeutralityBoundaryReference : String
a5TransferOperatorBiasNeutralityBoundaryReference =
  "DASHI.Physics.Closure.NSTransferOperatorBiasNeutralityBoundary"

a6PointwiseToAbelCompositeBoundaryReference : String
a6PointwiseToAbelCompositeBoundaryReference =
  "DASHI.Physics.Closure.NSPointwiseToAbelCompositeA6Boundary"

a6TheoremLadderBoundaryReference : String
a6TheoremLadderBoundaryReference =
  "DASHI.Physics.Closure.NSA6TheoremLadderBoundary"

a4NoAngularCollapseTransferCompositeBoundaryImported : Bool
a4NoAngularCollapseTransferCompositeBoundaryImported =
  true

a5TransferOperatorBiasNeutralityBoundaryImported : Bool
a5TransferOperatorBiasNeutralityBoundaryImported =
  true

a6PointwiseToAbelCompositeBoundaryImported : Bool
a6PointwiseToAbelCompositeBoundaryImported =
  true

a6TheoremLadderBoundaryImported : Bool
a6TheoremLadderBoundaryImported =
  true

record ImportedNSA4ToA6TransferLadderSupport : Set where
  field
    a4Boundary :
      A4.NSA4NoAngularCollapseTransferCompositeBoundary
    a4BoundaryIsCanonical :
      a4Boundary
        ≡ A4.canonicalNSA4NoAngularCollapseTransferCompositeBoundary
    a5BiasBoundary :
      A5Bias.NSTransferOperatorBiasNeutralityBoundary
    a5BiasBoundaryIsCanonical :
      a5BiasBoundary
        ≡ A5Bias.canonicalNSTransferOperatorBiasNeutralityBoundary
    a6CompositeBoundary :
      A6Abel.NSPointwiseToAbelCompositeA6Boundary
    a6CompositeBoundaryIsCanonical :
      a6CompositeBoundary
        ≡ A6Abel.canonicalNSPointwiseToAbelCompositeA6Boundary
    a6TheoremLadderBoundary :
      A6Ladder.NSA6TheoremLadderBoundary
    a6TheoremLadderBoundaryIsCanonical :
      a6TheoremLadderBoundary
        ≡ A6Ladder.canonicalNSA6TheoremLadderBoundary
    a4ImportedIsTrue :
      a4NoAngularCollapseTransferCompositeBoundaryImported ≡ true
    a5ImportedIsTrue :
      a5TransferOperatorBiasNeutralityBoundaryImported ≡ true
    a6CompositeImportedIsTrue :
      a6PointwiseToAbelCompositeBoundaryImported ≡ true
    a6LadderImportedIsTrue :
      a6TheoremLadderBoundaryImported ≡ true

    importedA4StillFalse :
      A4.A4NoAngularCollapseTransferTheoremProved ≡ false
    importedA4OutputSupportStillFalse :
      A4.A4LeiRenTianOutputSupportTransferProved ≡ false
    importedA5BiasStillFalse :
      A5Bias.typeIBiasBoundPromoted ≡ false
    importedA5PDETransferStillFalse :
      A5Bias.pdeTransferPromoted ≡ false
    importedA6CompositeStillFalse :
      A6Abel.a6PointwiseToAbelClosed ≡ false
    importedA6ResidualDepletionStillFalse :
      A6Abel.residualDepletionProved ≡ false
    importedA6LadderTheoremStillFalse :
      A6Ladder.A6TheoremProved ≡ false
    importedA6LadderTriadicStillFalse :
      A6Ladder.triadicCompensatedLeakageIdentityProved ≡ false
    importedA6LadderResidualStillFalse :
      A6Ladder.residualNonpositiveProved ≡ false
    importedA6LadderLocalDefectStillFalse :
      A6Ladder.localDefectMonotonicityProved ≡ false
    importedA6LadderClayStillFalse :
      A6Ladder.nsClayPromoted ≡ false

canonicalImportedNSA4ToA6TransferLadderSupport :
  ImportedNSA4ToA6TransferLadderSupport
canonicalImportedNSA4ToA6TransferLadderSupport =
  record
    { a4Boundary =
        A4.canonicalNSA4NoAngularCollapseTransferCompositeBoundary
    ; a4BoundaryIsCanonical =
        refl
    ; a5BiasBoundary =
        A5Bias.canonicalNSTransferOperatorBiasNeutralityBoundary
    ; a5BiasBoundaryIsCanonical =
        refl
    ; a6CompositeBoundary =
        A6Abel.canonicalNSPointwiseToAbelCompositeA6Boundary
    ; a6CompositeBoundaryIsCanonical =
        refl
    ; a6TheoremLadderBoundary =
        A6Ladder.canonicalNSA6TheoremLadderBoundary
    ; a6TheoremLadderBoundaryIsCanonical =
        refl
    ; a4ImportedIsTrue =
        refl
    ; a5ImportedIsTrue =
        refl
    ; a6CompositeImportedIsTrue =
        refl
    ; a6LadderImportedIsTrue =
        refl
    ; importedA4StillFalse =
        refl
    ; importedA4OutputSupportStillFalse =
        refl
    ; importedA5BiasStillFalse =
        refl
    ; importedA5PDETransferStillFalse =
        refl
    ; importedA6CompositeStillFalse =
        refl
    ; importedA6ResidualDepletionStillFalse =
        refl
    ; importedA6LadderTheoremStillFalse =
        refl
    ; importedA6LadderTriadicStillFalse =
        refl
    ; importedA6LadderResidualStillFalse =
        refl
    ; importedA6LadderLocalDefectStillFalse =
        refl
    ; importedA6LadderClayStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Ladder nodes and dependency edges.

data NSA4ToA6TransferLadderNode : Set where
  imported-A4-no-angular-collapse-output-support :
    NSA4ToA6TransferLadderNode
  conditional-A4-output-support-transfer-target :
    NSA4ToA6TransferLadderNode
  imported-A5-transfer-operator-bias-neutrality :
    NSA4ToA6TransferLadderNode
  conditional-A5-kappa-bias-vanishing-target :
    NSA4ToA6TransferLadderNode
  imported-A6-pointwise-to-Abel-composite :
    NSA4ToA6TransferLadderNode
  imported-A6-theorem-ladder :
    NSA4ToA6TransferLadderNode
  conditional-A6-leakage-identity-target :
    NSA4ToA6TransferLadderNode
  conditional-A7-residual-depletion-target :
    NSA4ToA6TransferLadderNode
  non-target-NS-Clay :
    NSA4ToA6TransferLadderNode

canonicalNSA4ToA6TransferLadderNodes :
  List NSA4ToA6TransferLadderNode
canonicalNSA4ToA6TransferLadderNodes =
  imported-A4-no-angular-collapse-output-support
  ∷ conditional-A4-output-support-transfer-target
  ∷ imported-A5-transfer-operator-bias-neutrality
  ∷ conditional-A5-kappa-bias-vanishing-target
  ∷ imported-A6-pointwise-to-Abel-composite
  ∷ imported-A6-theorem-ladder
  ∷ conditional-A6-leakage-identity-target
  ∷ conditional-A7-residual-depletion-target
  ∷ non-target-NS-Clay
  ∷ []

nsa4ToA6TransferLadderNodeCount : Nat
nsa4ToA6TransferLadderNodeCount =
  listLength canonicalNSA4ToA6TransferLadderNodes

nsa4ToA6TransferLadderNodeCountIs9 :
  nsa4ToA6TransferLadderNodeCount ≡ 9
nsa4ToA6TransferLadderNodeCountIs9 =
  refl

data NSA4ToA6TransferLadderEdge : Set where
  a4BoundaryToConditionalOutputSupport :
    NSA4ToA6TransferLadderEdge
  conditionalOutputSupportToA5BiasNeutrality :
    NSA4ToA6TransferLadderEdge
  a5BiasNeutralityToConditionalKappaBiasVanishing :
    NSA4ToA6TransferLadderEdge
  conditionalKappaBiasVanishingToA6PointwiseToAbel :
    NSA4ToA6TransferLadderEdge
  a6PointwiseToAbelToA6TheoremLadder :
    NSA4ToA6TransferLadderEdge
  a6TheoremLadderToLeakageIdentityTarget :
    NSA4ToA6TransferLadderEdge
  leakageIdentityToResidualDepletionTarget :
    NSA4ToA6TransferLadderEdge
  residualDepletionDoesNotPromoteNSClay :
    NSA4ToA6TransferLadderEdge

canonicalNSA4ToA6TransferLadderEdges :
  List NSA4ToA6TransferLadderEdge
canonicalNSA4ToA6TransferLadderEdges =
  a4BoundaryToConditionalOutputSupport
  ∷ conditionalOutputSupportToA5BiasNeutrality
  ∷ a5BiasNeutralityToConditionalKappaBiasVanishing
  ∷ conditionalKappaBiasVanishingToA6PointwiseToAbel
  ∷ a6PointwiseToAbelToA6TheoremLadder
  ∷ a6TheoremLadderToLeakageIdentityTarget
  ∷ leakageIdentityToResidualDepletionTarget
  ∷ residualDepletionDoesNotPromoteNSClay
  ∷ []

nsa4ToA6TransferLadderEdgeCount : Nat
nsa4ToA6TransferLadderEdgeCount =
  listLength canonicalNSA4ToA6TransferLadderEdges

nsa4ToA6TransferLadderEdgeCountIs8 :
  nsa4ToA6TransferLadderEdgeCount ≡ 8
nsa4ToA6TransferLadderEdgeCountIs8 =
  refl

------------------------------------------------------------------------
-- Conditional targets and fail-closed theorem flags.

transferLadderBoundaryRecorded : Bool
transferLadderBoundaryRecorded =
  true

conditionalA4OutputSupportTransferTargetRecorded : Bool
conditionalA4OutputSupportTransferTargetRecorded =
  true

conditionalA5KappaBiasVanishingTargetRecorded : Bool
conditionalA5KappaBiasVanishingTargetRecorded =
  true

conditionalA6LeakageIdentityTargetRecorded : Bool
conditionalA6LeakageIdentityTargetRecorded =
  true

conditionalA7ResidualDepletionTargetRecorded : Bool
conditionalA7ResidualDepletionTargetRecorded =
  true

A4OutputSupportTransferProved : Bool
A4OutputSupportTransferProved =
  false

A4NoAngularCollapseTheoremProved : Bool
A4NoAngularCollapseTheoremProved =
  false

A5KappaBiasVanishingProved : Bool
A5KappaBiasVanishingProved =
  false

A5TypeIBiasBoundPromoted : Bool
A5TypeIBiasBoundPromoted =
  false

A6PointwiseToAbelProved : Bool
A6PointwiseToAbelProved =
  false

A6LeakageIdentityProved : Bool
A6LeakageIdentityProved =
  false

A6ResidualNonpositiveProved : Bool
A6ResidualNonpositiveProved =
  false

A7ResidualDepletionProved : Bool
A7ResidualDepletionProved =
  false

A7LocalDefectMonotonicityProved : Bool
A7LocalDefectMonotonicityProved =
  false

NSClayPromoted : Bool
NSClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

data NSA4ToA6TransferLadderPromotion : Set where

nsa4ToA6TransferLadderPromotionImpossibleHere :
  NSA4ToA6TransferLadderPromotion →
  ⊥
nsa4ToA6TransferLadderPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Blockers and rows.

data NSA4ToA6TransferLadderBlocker : Set where
  blocker-A4-no-angular-collapse-output-support-unproved :
    NSA4ToA6TransferLadderBlocker
  blocker-A5-kappa-bias-vanishing-not-derived-from-neutrality :
    NSA4ToA6TransferLadderBlocker
  blocker-A5-PDE-transfer-to-actual-NS-measure-missing :
    NSA4ToA6TransferLadderBlocker
  blocker-A6-pointwise-to-Abel-theorem-unproved :
    NSA4ToA6TransferLadderBlocker
  blocker-A6-triadic-leakage-identity-unproved :
    NSA4ToA6TransferLadderBlocker
  blocker-A6-critical-residual-nonpositive-unproved :
    NSA4ToA6TransferLadderBlocker
  blocker-A7-residual-depletion-unproved :
    NSA4ToA6TransferLadderBlocker
  blocker-NS-Clay-promotion-forbidden-here :
    NSA4ToA6TransferLadderBlocker

canonicalNSA4ToA6TransferLadderBlockers :
  List NSA4ToA6TransferLadderBlocker
canonicalNSA4ToA6TransferLadderBlockers =
  blocker-A4-no-angular-collapse-output-support-unproved
  ∷ blocker-A5-kappa-bias-vanishing-not-derived-from-neutrality
  ∷ blocker-A5-PDE-transfer-to-actual-NS-measure-missing
  ∷ blocker-A6-pointwise-to-Abel-theorem-unproved
  ∷ blocker-A6-triadic-leakage-identity-unproved
  ∷ blocker-A6-critical-residual-nonpositive-unproved
  ∷ blocker-A7-residual-depletion-unproved
  ∷ blocker-NS-Clay-promotion-forbidden-here
  ∷ []

nsa4ToA6TransferLadderBlockerCount : Nat
nsa4ToA6TransferLadderBlockerCount =
  listLength canonicalNSA4ToA6TransferLadderBlockers

nsa4ToA6TransferLadderBlockerCountIs8 :
  nsa4ToA6TransferLadderBlockerCount ≡ 8
nsa4ToA6TransferLadderBlockerCountIs8 =
  refl

data NSA4ToA6TransferLadderRung : Set where
  rung-A4-output-support :
    NSA4ToA6TransferLadderRung
  rung-A5-kappa-bias-vanishing :
    NSA4ToA6TransferLadderRung
  rung-A6-pointwise-to-Abel :
    NSA4ToA6TransferLadderRung
  rung-A6-leakage-identity :
    NSA4ToA6TransferLadderRung
  rung-A7-residual-depletion :
    NSA4ToA6TransferLadderRung

canonicalNSA4ToA6TransferLadderRungs :
  List NSA4ToA6TransferLadderRung
canonicalNSA4ToA6TransferLadderRungs =
  rung-A4-output-support
  ∷ rung-A5-kappa-bias-vanishing
  ∷ rung-A6-pointwise-to-Abel
  ∷ rung-A6-leakage-identity
  ∷ rung-A7-residual-depletion
  ∷ []

nsa4ToA6TransferLadderRungCount : Nat
nsa4ToA6TransferLadderRungCount =
  listLength canonicalNSA4ToA6TransferLadderRungs

nsa4ToA6TransferLadderRungCountIs5 :
  nsa4ToA6TransferLadderRungCount ≡ 5
nsa4ToA6TransferLadderRungCountIs5 =
  refl

record NSA4ToA6TransferLadderRow : Set where
  field
    rung :
      NSA4ToA6TransferLadderRung
    sourceBoundary :
      String
    targetName :
      String
    blocker :
      NSA4ToA6TransferLadderBlocker
    conditionalTargetRecorded :
      Bool
    conditionalTargetRecordedIsTrue :
      conditionalTargetRecorded ≡ true
    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

a4OutputSupportRow : NSA4ToA6TransferLadderRow
a4OutputSupportRow =
  record
    { rung =
        rung-A4-output-support
    ; sourceBoundary =
        a4NoAngularCollapseTransferCompositeBoundaryReference
    ; targetName =
        "conditional A4 no-angular-collapse/output-support transfer"
    ; blocker =
        blocker-A4-no-angular-collapse-output-support-unproved
    ; conditionalTargetRecorded =
        conditionalA4OutputSupportTransferTargetRecorded
    ; conditionalTargetRecordedIsTrue =
        refl
    ; theoremPromoted =
        A4OutputSupportTransferProved
    ; theoremPromotedIsFalse =
        refl
    }

a5KappaBiasVanishingRow : NSA4ToA6TransferLadderRow
a5KappaBiasVanishingRow =
  record
    { rung =
        rung-A5-kappa-bias-vanishing
    ; sourceBoundary =
        a5TransferOperatorBiasNeutralityBoundaryReference
    ; targetName =
        "conditional A5 kappa-bias vanishing after A4 output-support transfer"
    ; blocker =
        blocker-A5-kappa-bias-vanishing-not-derived-from-neutrality
    ; conditionalTargetRecorded =
        conditionalA5KappaBiasVanishingTargetRecorded
    ; conditionalTargetRecordedIsTrue =
        refl
    ; theoremPromoted =
        A5KappaBiasVanishingProved
    ; theoremPromotedIsFalse =
        refl
    }

a6PointwiseToAbelRow : NSA4ToA6TransferLadderRow
a6PointwiseToAbelRow =
  record
    { rung =
        rung-A6-pointwise-to-Abel
    ; sourceBoundary =
        a6PointwiseToAbelCompositeBoundaryReference
    ; targetName =
        "conditional A6 pointwise-to-Abel transfer after A5 bias vanishing"
    ; blocker =
        blocker-A6-pointwise-to-Abel-theorem-unproved
    ; conditionalTargetRecorded =
        conditionalA6LeakageIdentityTargetRecorded
    ; conditionalTargetRecordedIsTrue =
        refl
    ; theoremPromoted =
        A6PointwiseToAbelProved
    ; theoremPromotedIsFalse =
        refl
    }

a6LeakageIdentityRow : NSA4ToA6TransferLadderRow
a6LeakageIdentityRow =
  record
    { rung =
        rung-A6-leakage-identity
    ; sourceBoundary =
        a6TheoremLadderBoundaryReference
    ; targetName =
        "conditional A6 compensated leakage identity"
    ; blocker =
        blocker-A6-triadic-leakage-identity-unproved
    ; conditionalTargetRecorded =
        conditionalA6LeakageIdentityTargetRecorded
    ; conditionalTargetRecordedIsTrue =
        refl
    ; theoremPromoted =
        A6LeakageIdentityProved
    ; theoremPromotedIsFalse =
        refl
    }

a7ResidualDepletionRow : NSA4ToA6TransferLadderRow
a7ResidualDepletionRow =
  record
    { rung =
        rung-A7-residual-depletion
    ; sourceBoundary =
        a6TheoremLadderBoundaryReference
    ; targetName =
        "conditional A7 residual depletion after A6 leakage identity"
    ; blocker =
        blocker-A7-residual-depletion-unproved
    ; conditionalTargetRecorded =
        conditionalA7ResidualDepletionTargetRecorded
    ; conditionalTargetRecordedIsTrue =
        refl
    ; theoremPromoted =
        A7ResidualDepletionProved
    ; theoremPromotedIsFalse =
        refl
    }

canonicalNSA4ToA6TransferLadderRows :
  List NSA4ToA6TransferLadderRow
canonicalNSA4ToA6TransferLadderRows =
  a4OutputSupportRow
  ∷ a5KappaBiasVanishingRow
  ∷ a6PointwiseToAbelRow
  ∷ a6LeakageIdentityRow
  ∷ a7ResidualDepletionRow
  ∷ []

nsa4ToA6TransferLadderRowCount : Nat
nsa4ToA6TransferLadderRowCount =
  listLength canonicalNSA4ToA6TransferLadderRows

nsa4ToA6TransferLadderRowCountIs5 :
  nsa4ToA6TransferLadderRowCount ≡ 5
nsa4ToA6TransferLadderRowCountIs5 =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F.

dependencyLadderSummary : String
dependencyLadderSummary =
  "A4 no-angular-collapse/output-support transfer -> A5 kappa-bias vanishing -> A6 pointwise-to-Abel and compensated leakage identity -> A7 residual depletion"

organizationString : String
organizationString =
  "O: Closure boundary ledger for the NS transfer ladder spanning imported A4 output-support, A5 finite bias-neutrality, A6 Abel/leakage receipts, and the conditional A7 residual-depletion target."

requirementString : String
requirementString =
  "R: Record the dependency ladder A4 no-angular-collapse/output-support transfer -> A5 kappa-bias vanishing -> A6 pointwise-to-Abel/leakage identity -> A7 residual depletion without promoting any theorem."

codeArtifactString : String
codeArtifactString =
  "C: NSA4ToA6TransferLadderBoundary imports NSA4NoAngularCollapseTransferCompositeBoundary, NSTransferOperatorBiasNeutralityBoundary, NSPointwiseToAbelCompositeA6Boundary, and NSA6TheoremLadderBoundary."

stateString : String
stateString =
  "S: All four dependency surfaces are imported and typed; conditional targets are recorded, while A4, A5, A6, A7, NS Clay, and terminal promotion flags remain false."

latticeString : String
latticeString =
  "L: ordered nodes and edges enforce A4 output support before A5 bias vanishing, A5 before A6 Abel/leakage, A6 before A7 residual depletion, with NS Clay outside the promoted target set."

proposalString : String
proposalString =
  "P: Discharge blockers in ladder order: prove A4 output support, derive actual kappa-bias vanishing from neutrality plus PDE transfer, promote A6 Abel/leakage, then prove residual depletion."

governanceString : String
governanceString =
  "G: Fail closed: only conditional targets are recorded; no imported receipt is reinterpreted as a theorem and no Clay or terminal claim is promoted."

gapString : String
gapString =
  "F: Missing theorem-grade A4 transfer, A5 kappa-bias vanishing and PDE measure transfer, A6 pointwise-to-Abel and compensated leakage identity, critical residual nonpositivity, and A7 residual depletion."

------------------------------------------------------------------------
-- Boundary record.

record NSA4ToA6TransferLadderBoundary : Set where
  field
    importedSupport :
      ImportedNSA4ToA6TransferLadderSupport
    importedSupportIsCanonical :
      importedSupport ≡ canonicalImportedNSA4ToA6TransferLadderSupport
    nodes :
      List NSA4ToA6TransferLadderNode
    nodesAreCanonical :
      nodes ≡ canonicalNSA4ToA6TransferLadderNodes
    nodeCountProof :
      nsa4ToA6TransferLadderNodeCount ≡ 9
    edges :
      List NSA4ToA6TransferLadderEdge
    edgesAreCanonical :
      edges ≡ canonicalNSA4ToA6TransferLadderEdges
    edgeCountProof :
      nsa4ToA6TransferLadderEdgeCount ≡ 8
    rungs :
      List NSA4ToA6TransferLadderRung
    rungsAreCanonical :
      rungs ≡ canonicalNSA4ToA6TransferLadderRungs
    rungCountProof :
      nsa4ToA6TransferLadderRungCount ≡ 5
    rows :
      List NSA4ToA6TransferLadderRow
    rowsAreCanonical :
      rows ≡ canonicalNSA4ToA6TransferLadderRows
    rowCountProof :
      nsa4ToA6TransferLadderRowCount ≡ 5
    blockers :
      List NSA4ToA6TransferLadderBlocker
    blockersAreCanonical :
      blockers ≡ canonicalNSA4ToA6TransferLadderBlockers
    blockerCountProof :
      nsa4ToA6TransferLadderBlockerCount ≡ 8
    dependencyLadder :
      String
    dependencyLadderIsCanonical :
      dependencyLadder ≡ dependencyLadderSummary
    O :
      String
    OIsCanonical :
      O ≡ organizationString
    R :
      String
    RIsCanonical :
      R ≡ requirementString
    C :
      String
    CIsCanonical :
      C ≡ codeArtifactString
    S :
      String
    SIsCanonical :
      S ≡ stateString
    L :
      String
    LIsCanonical :
      L ≡ latticeString
    P :
      String
    PIsCanonical :
      P ≡ proposalString
    G :
      String
    GIsCanonical :
      G ≡ governanceString
    F :
      String
    FIsCanonical :
      F ≡ gapString

    boundaryRecordedIsTrue :
      transferLadderBoundaryRecorded ≡ true
    conditionalA4TargetRecordedIsTrue :
      conditionalA4OutputSupportTransferTargetRecorded ≡ true
    conditionalA5TargetRecordedIsTrue :
      conditionalA5KappaBiasVanishingTargetRecorded ≡ true
    conditionalA6TargetRecordedIsTrue :
      conditionalA6LeakageIdentityTargetRecorded ≡ true
    conditionalA7TargetRecordedIsTrue :
      conditionalA7ResidualDepletionTargetRecorded ≡ true

    A4OutputSupportTransferProvedIsFalse :
      A4OutputSupportTransferProved ≡ false
    A4NoAngularCollapseTheoremProvedIsFalse :
      A4NoAngularCollapseTheoremProved ≡ false
    A5KappaBiasVanishingProvedIsFalse :
      A5KappaBiasVanishingProved ≡ false
    A5TypeIBiasBoundPromotedIsFalse :
      A5TypeIBiasBoundPromoted ≡ false
    A6PointwiseToAbelProvedIsFalse :
      A6PointwiseToAbelProved ≡ false
    A6LeakageIdentityProvedIsFalse :
      A6LeakageIdentityProved ≡ false
    A6ResidualNonpositiveProvedIsFalse :
      A6ResidualNonpositiveProved ≡ false
    A7ResidualDepletionProvedIsFalse :
      A7ResidualDepletionProved ≡ false
    A7LocalDefectMonotonicityProvedIsFalse :
      A7LocalDefectMonotonicityProved ≡ false
    NSClayPromotedIsFalse :
      NSClayPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    importedA4TheoremStillFalse :
      A4.A4NoAngularCollapseTransferTheoremProved ≡ false
    importedA4OutputSupportStillFalse :
      A4.A4LeiRenTianOutputSupportTransferProved ≡ false
    importedA5TypeIBiasStillFalse :
      A5Bias.typeIBiasBoundPromoted ≡ false
    importedA5ClayStillFalse :
      A5Bias.clayNavierStokesPromoted ≡ false
    importedA6CompositeStillFalse :
      A6Abel.a6PointwiseToAbelClosed ≡ false
    importedA6CompositeResidualDepletionStillFalse :
      A6Abel.residualDepletionProved ≡ false
    importedA6LadderTheoremStillFalse :
      A6Ladder.A6TheoremProved ≡ false
    importedA6LadderTriadicStillFalse :
      A6Ladder.triadicCompensatedLeakageIdentityProved ≡ false
    importedA6LadderResidualStillFalse :
      A6Ladder.residualNonpositiveProved ≡ false
    importedA6LadderClayStillFalse :
      A6Ladder.nsClayPromoted ≡ false

canonicalNSA4ToA6TransferLadderBoundary :
  NSA4ToA6TransferLadderBoundary
canonicalNSA4ToA6TransferLadderBoundary =
  record
    { importedSupport =
        canonicalImportedNSA4ToA6TransferLadderSupport
    ; importedSupportIsCanonical =
        refl
    ; nodes =
        canonicalNSA4ToA6TransferLadderNodes
    ; nodesAreCanonical =
        refl
    ; nodeCountProof =
        refl
    ; edges =
        canonicalNSA4ToA6TransferLadderEdges
    ; edgesAreCanonical =
        refl
    ; edgeCountProof =
        refl
    ; rungs =
        canonicalNSA4ToA6TransferLadderRungs
    ; rungsAreCanonical =
        refl
    ; rungCountProof =
        refl
    ; rows =
        canonicalNSA4ToA6TransferLadderRows
    ; rowsAreCanonical =
        refl
    ; rowCountProof =
        refl
    ; blockers =
        canonicalNSA4ToA6TransferLadderBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCountProof =
        refl
    ; dependencyLadder =
        dependencyLadderSummary
    ; dependencyLadderIsCanonical =
        refl
    ; O =
        organizationString
    ; OIsCanonical =
        refl
    ; R =
        requirementString
    ; RIsCanonical =
        refl
    ; C =
        codeArtifactString
    ; CIsCanonical =
        refl
    ; S =
        stateString
    ; SIsCanonical =
        refl
    ; L =
        latticeString
    ; LIsCanonical =
        refl
    ; P =
        proposalString
    ; PIsCanonical =
        refl
    ; G =
        governanceString
    ; GIsCanonical =
        refl
    ; F =
        gapString
    ; FIsCanonical =
        refl
    ; boundaryRecordedIsTrue =
        refl
    ; conditionalA4TargetRecordedIsTrue =
        refl
    ; conditionalA5TargetRecordedIsTrue =
        refl
    ; conditionalA6TargetRecordedIsTrue =
        refl
    ; conditionalA7TargetRecordedIsTrue =
        refl
    ; A4OutputSupportTransferProvedIsFalse =
        refl
    ; A4NoAngularCollapseTheoremProvedIsFalse =
        refl
    ; A5KappaBiasVanishingProvedIsFalse =
        refl
    ; A5TypeIBiasBoundPromotedIsFalse =
        refl
    ; A6PointwiseToAbelProvedIsFalse =
        refl
    ; A6LeakageIdentityProvedIsFalse =
        refl
    ; A6ResidualNonpositiveProvedIsFalse =
        refl
    ; A7ResidualDepletionProvedIsFalse =
        refl
    ; A7LocalDefectMonotonicityProvedIsFalse =
        refl
    ; NSClayPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    ; importedA4TheoremStillFalse =
        refl
    ; importedA4OutputSupportStillFalse =
        refl
    ; importedA5TypeIBiasStillFalse =
        refl
    ; importedA5ClayStillFalse =
        refl
    ; importedA6CompositeStillFalse =
        refl
    ; importedA6CompositeResidualDepletionStillFalse =
        refl
    ; importedA6LadderTheoremStillFalse =
        refl
    ; importedA6LadderTriadicStillFalse =
        refl
    ; importedA6LadderResidualStillFalse =
        refl
    ; importedA6LadderClayStillFalse =
        refl
    }

------------------------------------------------------------------------
-- External fail-closed checks.

keepsA4False :
  A4NoAngularCollapseTheoremProved ≡ false
keepsA4False =
  refl

keepsA5False :
  A5KappaBiasVanishingProved ≡ false
keepsA5False =
  refl

keepsA6False :
  A6LeakageIdentityProved ≡ false
keepsA6False =
  refl

keepsA7False :
  A7ResidualDepletionProved ≡ false
keepsA7False =
  refl

keepsNSClayFalse :
  NSClayPromoted ≡ false
keepsNSClayFalse =
  refl

keepsTerminalFalse :
  terminalPromotion ≡ false
keepsTerminalFalse =
  refl

postulate
  nsa4ToA6TransferLadderDoesNotProveA4 :
    A4NoAngularCollapseTheoremProved ≡ true →
    ⊥

  nsa4ToA6TransferLadderDoesNotProveA5 :
    A5KappaBiasVanishingProved ≡ true →
    ⊥

  nsa4ToA6TransferLadderDoesNotProveA6 :
    A6LeakageIdentityProved ≡ true →
    ⊥

  nsa4ToA6TransferLadderDoesNotProveA7 :
    A7ResidualDepletionProved ≡ true →
    ⊥

  nsa4ToA6TransferLadderDoesNotPromoteNSClay :
    NSClayPromoted ≡ true →
    ⊥

  nsa4ToA6TransferLadderDoesNotPromoteTerminal :
    terminalPromotion ≡ true →
    ⊥
