module DASHI.Physics.Closure.NSPointwiseToAbelCompositeA6Boundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSAbelShellMixingLLNBoundary
  as LLN
import DASHI.Physics.Closure.NSDiagonalStretchingToAbelMeanBoundary
  as Diagonal
import DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary
  as Localization
import DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary
  as OffDiagonal
import DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary
  as Parent

------------------------------------------------------------------------
-- NS A6 pointwise-to-Abel composite boundary.
--
-- This fail-closed receipt ties the A6 parent boundary to the current child
-- receipts:
--
--   * NSDiagonalStretchingToAbelMeanBoundary
--   * NSOffDiagonalShellAbsorptionBoundary
--   * NSAbelShellMixingLLNBoundary
--
-- The composite records dependency order and blockers only; it does not
-- prove A6, residual monotonicity, residual depletion, NS Clay, or any
-- terminal promotion.

sharpenedA1PackageReference : String
sharpenedA1PackageReference =
  "DASHI.Physics.Closure.NSA1TypeILorentzToAbelMassRouteTheoremBoundary"

sharpenedA3PackageReference : String
sharpenedA3PackageReference =
  "DASHI.Physics.Closure.NSQuantitativeStationarityRateBoundary"

sharpenedA4PackageReference : String
sharpenedA4PackageReference =
  "DASHI.Physics.Closure.NSA4ResidualPositiveTheoremLadderBoundary"

sharpenedA5ConsumerReference : String
sharpenedA5ConsumerReference =
  "DASHI.Physics.Closure.NSA5KappaBiasVanishingFromA4StationarityBoundary"

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
-- Imported and expected receipt references.

a6ParentBoundaryReference : String
a6ParentBoundaryReference =
  "DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary"

diagonalChildBoundaryReference : String
diagonalChildBoundaryReference =
  "DASHI.Physics.Closure.NSDiagonalStretchingToAbelMeanBoundary"

offDiagonalChildBoundaryReference : String
offDiagonalChildBoundaryReference =
  "DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary"

llnChildBoundaryReference : String
llnChildBoundaryReference =
  "DASHI.Physics.Closure.NSAbelShellMixingLLNBoundary"

localizationChildBoundaryReference : String
localizationChildBoundaryReference =
  "DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary"

localizationChildExpectedSummary : String
localizationChildExpectedSummary =
  "Imported localization child: localized cutoff, Leray pressure, and commutator control for the A6 pointwise-to-Abel replacement."

a6ParentImported : Bool
a6ParentImported =
  true

diagonalChildTyped : Bool
diagonalChildTyped =
  true

offDiagonalChildTyped : Bool
offDiagonalChildTyped =
  true

llnChildTyped : Bool
llnChildTyped =
  true

localizationChildExpected : Bool
localizationChildExpected =
  true

localizationChildOpen : Bool
localizationChildOpen =
  true

localizationChildImported : Bool
localizationChildImported =
  true

sharpenedA1A3A4PackageConsumedRecorded : Bool
sharpenedA1A3A4PackageConsumedRecorded =
  true

compositeTheoremProved : Bool
compositeTheoremProved =
  false

a6PointwiseToAbelClosed : Bool
a6PointwiseToAbelClosed =
  false

residualMonotonicityProved : Bool
residualMonotonicityProved =
  false

residualDepletionProved : Bool
residualDepletionProved =
  false

nsClayPromoted : Bool
nsClayPromoted =
  false

terminalUnificationPromoted : Bool
terminalUnificationPromoted =
  false

record ImportedCompositeA6Support : Set where
  field
    parentBoundary :
      Parent.NSPointwiseToAbelAveragingBoundary
    parentBoundaryIsCanonical :
      parentBoundary
        ≡ Parent.canonicalNSPointwiseToAbelAveragingBoundary
    diagonalChild :
      Diagonal.NSDiagonalStretchingToAbelMeanBoundary
    diagonalChildIsCanonical :
      diagonalChild
        ≡ Diagonal.canonicalNSDiagonalStretchingToAbelMeanBoundary
    offDiagonalChild :
      OffDiagonal.NSOffDiagonalShellAbsorptionBoundary
    offDiagonalChildIsCanonical :
      offDiagonalChild
        ≡ OffDiagonal.canonicalNSOffDiagonalShellAbsorptionBoundary
    llnChild :
      LLN.NSAbelShellMixingLLNBoundary
    llnChildIsCanonical :
      llnChild
        ≡ LLN.canonicalNSAbelShellMixingLLNBoundary
    localizationChild :
      Localization.NSLocalizationPressureCommutatorBoundary
    localizationChildIsCanonical :
      localizationChild
        ≡ Localization.canonicalNSLocalizationPressureCommutatorBoundary
    a6ParentImportedIsTrue :
      a6ParentImported ≡ true
    diagonalChildTypedIsTrue :
      diagonalChildTyped ≡ true
    offDiagonalChildTypedIsTrue :
      offDiagonalChildTyped ≡ true
    llnChildTypedIsTrue :
      llnChildTyped ≡ true
    localizationChildExpectedIsTrue :
      localizationChildExpected ≡ true
    localizationChildOpenIsTrue :
      localizationChildOpen ≡ true
    localizationChildImportedIsTrue :
      localizationChildImported ≡ true

canonicalImportedCompositeA6Support :
  ImportedCompositeA6Support
canonicalImportedCompositeA6Support =
  record
    { parentBoundary =
        Parent.canonicalNSPointwiseToAbelAveragingBoundary
    ; parentBoundaryIsCanonical =
        refl
    ; diagonalChild =
        Diagonal.canonicalNSDiagonalStretchingToAbelMeanBoundary
    ; diagonalChildIsCanonical =
        refl
    ; offDiagonalChild =
        OffDiagonal.canonicalNSOffDiagonalShellAbsorptionBoundary
    ; offDiagonalChildIsCanonical =
        refl
    ; llnChild =
        LLN.canonicalNSAbelShellMixingLLNBoundary
    ; llnChildIsCanonical =
        refl
    ; localizationChild =
        Localization.canonicalNSLocalizationPressureCommutatorBoundary
    ; localizationChildIsCanonical =
        refl
    ; a6ParentImportedIsTrue =
        refl
    ; diagonalChildTypedIsTrue =
        refl
    ; offDiagonalChildTypedIsTrue =
        refl
    ; llnChildTypedIsTrue =
        refl
    ; localizationChildExpectedIsTrue =
        refl
    ; localizationChildOpenIsTrue =
        refl
    ; localizationChildImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Dependency DAG.

data CompositeA6DependencyNode : Set where
  parent-NSPointwiseToAbelAveragingBoundary :
    CompositeA6DependencyNode
  child-NSDiagonalStretchingToAbelMeanBoundary :
    CompositeA6DependencyNode
  child-NSOffDiagonalShellAbsorptionBoundary :
    CompositeA6DependencyNode
  child-NSAbelShellMixingLLNBoundary :
    CompositeA6DependencyNode
  expected-NSLocalizationPressureCommutatorBoundary :
    CompositeA6DependencyNode
  target-TriadicCompensatedLeakageIdentityA6 :
    CompositeA6DependencyNode
  target-ResidualMonotonicity :
    CompositeA6DependencyNode
  target-NSClay :
    CompositeA6DependencyNode

canonicalCompositeA6DependencyNodes :
  List CompositeA6DependencyNode
canonicalCompositeA6DependencyNodes =
  parent-NSPointwiseToAbelAveragingBoundary
  ∷ child-NSDiagonalStretchingToAbelMeanBoundary
  ∷ child-NSOffDiagonalShellAbsorptionBoundary
  ∷ child-NSAbelShellMixingLLNBoundary
  ∷ expected-NSLocalizationPressureCommutatorBoundary
  ∷ target-TriadicCompensatedLeakageIdentityA6
  ∷ target-ResidualMonotonicity
  ∷ target-NSClay
  ∷ []

compositeA6DependencyNodeCount : Nat
compositeA6DependencyNodeCount =
  listLength canonicalCompositeA6DependencyNodes

compositeA6DependencyNodeCountIs8 :
  compositeA6DependencyNodeCount ≡ 8
compositeA6DependencyNodeCountIs8 =
  refl

data CompositeA6DependencyEdge : Set where
  parentToDiagonalChild :
    CompositeA6DependencyEdge
  parentToOffDiagonalChild :
    CompositeA6DependencyEdge
  parentToLLNChild :
    CompositeA6DependencyEdge
  parentToLocalizationChild :
    CompositeA6DependencyEdge
  diagonalChildToA6Target :
    CompositeA6DependencyEdge
  offDiagonalChildToA6Target :
    CompositeA6DependencyEdge
  llnChildToA6Target :
    CompositeA6DependencyEdge
  localizationChildToA6Target :
    CompositeA6DependencyEdge
  a6TargetToResidualMonotonicity :
    CompositeA6DependencyEdge
  residualMonotonicityToNSClay :
    CompositeA6DependencyEdge

canonicalCompositeA6DependencyEdges :
  List CompositeA6DependencyEdge
canonicalCompositeA6DependencyEdges =
  parentToDiagonalChild
  ∷ parentToOffDiagonalChild
  ∷ parentToLLNChild
  ∷ parentToLocalizationChild
  ∷ diagonalChildToA6Target
  ∷ offDiagonalChildToA6Target
  ∷ llnChildToA6Target
  ∷ localizationChildToA6Target
  ∷ a6TargetToResidualMonotonicity
  ∷ residualMonotonicityToNSClay
  ∷ []

compositeA6DependencyEdgeCount : Nat
compositeA6DependencyEdgeCount =
  listLength canonicalCompositeA6DependencyEdges

compositeA6DependencyEdgeCountIs10 :
  compositeA6DependencyEdgeCount ≡ 10
compositeA6DependencyEdgeCountIs10 =
  refl

data A6EnstrophyLeakageRouteClause : Set where
  a61-localized-enstrophy-ode-starting-from-partial-t-dr-plus-lambda-r-dr :
    A6EnstrophyLeakageRouteClause
  a62-transport-term-cancelled-up-to-localization-commutator :
    A6EnstrophyLeakageRouteClause
  a63-stretching-split-into-diagonal-offdiagonal-shells :
    A6EnstrophyLeakageRouteClause
  a64-pressure-and-cutoff-errors-routed-to-localization-child :
    A6EnstrophyLeakageRouteClause
  a65-bony-paraproduct-replacement-with-order-ninv-correction :
    A6EnstrophyLeakageRouteClause
  a66-pointwise-to-abel-shell-mean-transfer :
    A6EnstrophyLeakageRouteClause
  a67-a5-bias-vanishing-absorbed-into-epsilon-budget :
    A6EnstrophyLeakageRouteClause
  a68-assembled-inequality-partial-t-dr-plus-quarter-epsilon-c-lambda-dr :
    A6EnstrophyLeakageRouteClause

canonicalA6EnstrophyLeakageRouteClauses :
  List A6EnstrophyLeakageRouteClause
canonicalA6EnstrophyLeakageRouteClauses =
  a61-localized-enstrophy-ode-starting-from-partial-t-dr-plus-lambda-r-dr
  ∷ a62-transport-term-cancelled-up-to-localization-commutator
  ∷ a63-stretching-split-into-diagonal-offdiagonal-shells
  ∷ a64-pressure-and-cutoff-errors-routed-to-localization-child
  ∷ a65-bony-paraproduct-replacement-with-order-ninv-correction
  ∷ a66-pointwise-to-abel-shell-mean-transfer
  ∷ a67-a5-bias-vanishing-absorbed-into-epsilon-budget
  ∷ a68-assembled-inequality-partial-t-dr-plus-quarter-epsilon-c-lambda-dr
  ∷ []

a6EnstrophyLeakageRouteClauseCount : Nat
a6EnstrophyLeakageRouteClauseCount =
  listLength canonicalA6EnstrophyLeakageRouteClauses

a6EnstrophyLeakageRouteClauseCountIs8 :
  a6EnstrophyLeakageRouteClauseCount ≡ 8
a6EnstrophyLeakageRouteClauseCountIs8 =
  refl

data A6TransportCommutatorStretchingClause : Set where
  transportPartIsConvertedToCutoffCommutator :
    A6TransportCommutatorStretchingClause
  localizationCommutatorFeedsPressureSubBudget :
    A6TransportCommutatorStretchingClause
  diagonalStretchingFeedsAbelMeanMainTerm :
    A6TransportCommutatorStretchingClause
  offDiagonalStretchingFeedsShellAbsorption :
    A6TransportCommutatorStretchingClause
  shellMixingLlnConvertsFiniteWindowToAbelAverage :
    A6TransportCommutatorStretchingClause

canonicalA6TransportCommutatorStretchingClauses :
  List A6TransportCommutatorStretchingClause
canonicalA6TransportCommutatorStretchingClauses =
  transportPartIsConvertedToCutoffCommutator
  ∷ localizationCommutatorFeedsPressureSubBudget
  ∷ diagonalStretchingFeedsAbelMeanMainTerm
  ∷ offDiagonalStretchingFeedsShellAbsorption
  ∷ shellMixingLlnConvertsFiniteWindowToAbelAverage
  ∷ []

a6TransportCommutatorStretchingClauseCount : Nat
a6TransportCommutatorStretchingClauseCount =
  listLength canonicalA6TransportCommutatorStretchingClauses

a6TransportCommutatorStretchingClauseCountIs5 :
  a6TransportCommutatorStretchingClauseCount ≡ 5
a6TransportCommutatorStretchingClauseCountIs5 =
  refl

data A6EffectiveBudgetLine : Set where
  budget-main-damping-quarter-epsilon0-c-lambda :
    A6EffectiveBudgetLine
  budget-diagonal-abel-main-term :
    A6EffectiveBudgetLine
  budget-offdiagonal-shell-absorption :
    A6EffectiveBudgetLine
  budget-localization-pressure-commutator :
    A6EffectiveBudgetLine
  budget-bony-ninv-remainder :
    A6EffectiveBudgetLine
  budget-a5-bias-vanishing-gain :
    A6EffectiveBudgetLine

canonicalA6EffectiveBudgetLines :
  List A6EffectiveBudgetLine
canonicalA6EffectiveBudgetLines =
  budget-main-damping-quarter-epsilon0-c-lambda
  ∷ budget-diagonal-abel-main-term
  ∷ budget-offdiagonal-shell-absorption
  ∷ budget-localization-pressure-commutator
  ∷ budget-bony-ninv-remainder
  ∷ budget-a5-bias-vanishing-gain
  ∷ []

a6EffectiveBudgetLineCount : Nat
a6EffectiveBudgetLineCount =
  listLength canonicalA6EffectiveBudgetLines

a6EffectiveBudgetLineCountIs6 :
  a6EffectiveBudgetLineCount ≡ 6
a6EffectiveBudgetLineCountIs6 =
  refl

a6EnstrophyLeakageRouteTheoremText : String
a6EnstrophyLeakageRouteTheoremText =
  "A6 candidate theorem grammar: start from the localized enstrophy identity for D_r, split transport, stretching, pressure, and cutoff pieces, route transport into a localization commutator, split stretching into diagonal and off-diagonal shell interactions, replace the pointwise main term by the Abel shell mean using the diagonal/off-diagonal/LLN children, absorb A5 bias and O(N^-1) Bony remainder into the effective epsilon budget, and record the assembled inequality ∂t D_r + (ε0/4)c_lambda D_r <= C_eff D_r^(1+alpha)."

a6AssembledInequalityShape : String
a6AssembledInequalityShape =
  "Exact A6 inequality shape: ∂t D_r + ((ε0 / 4) c_lambda) D_r <= C_eff D_r^(1+alpha), where C_eff is the fail-closed aggregate of diagonal Abel main-term normalization, off-diagonal shell absorption leakage, localization/pressure commutator cost, and O(N^-1) paraproduct remainder."

a6TransportCommutatorStretchingSummary : String
a6TransportCommutatorStretchingSummary =
  "Decomposition grammar: transport is cancelled except for cutoff/localization commutators; stretching is split into diagonal shell interactions, off-diagonal shell leakage, and Abel shell-mixing transfer; pressure and cutoff terms are delegated to the localization child before final A6 assembly."

a6EffectiveBudgetSummary : String
a6EffectiveBudgetSummary =
  "Effective constants/budgets: retain a quarter of ε0*c_lambda as damping, book the diagonal Abel term as the main source coefficient, require off-diagonal and localization/pressure costs to be absorbable, and keep the Bony O(N^-1) remainder plus A5 bias contribution strictly inside the residual source constant C_eff."

dependencyDAGSummary : String
dependencyDAGSummary =
  "A6 consumes the sharpened A1/A3/A4 package through the recorded A5 consumer, then the A6 parent fans out to diagonal, offdiag, LLN, and localization children; all four children must feed the exact transport/commutator/stretching route and assembled inequality before any residual monotonicity, A7 depletion, or NS Clay claim can be considered."

------------------------------------------------------------------------
-- Remaining blockers and fail-closed summary.

data CompositeA6Blocker : Set where
  localizationPressureCommutatorChildMissing :
    CompositeA6Blocker
  diagonalChildIsBoundaryNotTheorem :
    CompositeA6Blocker
  offDiagonalChildIsBoundaryNotTheorem :
    CompositeA6Blocker
  llnChildIsBoundaryNotTheorem :
    CompositeA6Blocker
  pointwiseToAbelA6TheoremStillFalse :
    CompositeA6Blocker
  residualMonotonicityStillFalse :
    CompositeA6Blocker
  nsClayPromotionStillFalse :
    CompositeA6Blocker

canonicalCompositeA6Blockers : List CompositeA6Blocker
canonicalCompositeA6Blockers =
  localizationPressureCommutatorChildMissing
  ∷ diagonalChildIsBoundaryNotTheorem
  ∷ offDiagonalChildIsBoundaryNotTheorem
  ∷ llnChildIsBoundaryNotTheorem
  ∷ pointwiseToAbelA6TheoremStillFalse
  ∷ residualMonotonicityStillFalse
  ∷ nsClayPromotionStillFalse
  ∷ []

compositeA6BlockerCount : Nat
compositeA6BlockerCount =
  listLength canonicalCompositeA6Blockers

compositeA6BlockerCountIs7 :
  compositeA6BlockerCount ≡ 7
compositeA6BlockerCountIs7 =
  refl

compositeA6BlockerName : CompositeA6Blocker → String
compositeA6BlockerName localizationPressureCommutatorChildMissing =
  "missingNSLocalizationPressureCommutatorTheoremInput"
compositeA6BlockerName diagonalChildIsBoundaryNotTheorem =
  "missingNSDiagonalStretchingToAbelMeanTheorem"
compositeA6BlockerName offDiagonalChildIsBoundaryNotTheorem =
  "missingNSOffDiagonalShellAbsorptionTheorem"
compositeA6BlockerName llnChildIsBoundaryNotTheorem =
  "missingNSAbelShellMixingLLNTheorem"
compositeA6BlockerName pointwiseToAbelA6TheoremStillFalse =
  "missingA6PointwiseToAbelCompositeTheorem"
compositeA6BlockerName residualMonotonicityStillFalse =
  "missingA7ResidualDepletionOrMonotonicityPromotion"
compositeA6BlockerName nsClayPromotionStillFalse =
  "missingNSClayAuthorityAfterA6A9"

remainingBlockersSummary : String
remainingBlockersSummary =
  "Remaining blockers: upgrade localization, diagonal, off-diagonal, and LLN children to theorem inputs; assemble the exact A6 transport/commutator/stretching route through ∂t D_r + (ε0/4)c_lambda D_r <= C_eff D_r^(1+alpha); then prove A7 residual depletion. NS Clay remains false."

orcsLpgfSummary : String
orcsLpgfSummary =
  "O downstream A6 consumer surface; R record exact A6 inequality shape, transport/commutator/stretching decomposition, and effective budgets while consuming the sharpened A1/A3/A4 package through A5; C fail-closed Agda composite; S all theorem promotions remain false; L A1/A3/A4 -> A5 -> exact A6 assembly -> A7 -> A8/A9 order is explicit; P promote child theorems before assembling the A6 inequality; G no Clay promotion; F A6 theorem, A7 depletion, and downstream closure remain false."

------------------------------------------------------------------------
-- Canonical composite receipt.

record NSPointwiseToAbelCompositeA6Boundary : Set where
  field
    importedSupport :
      ImportedCompositeA6Support
    dependencyNodes :
      List CompositeA6DependencyNode
    dependencyNodeCountProof :
      compositeA6DependencyNodeCount ≡ 8
    dependencyEdges :
      List CompositeA6DependencyEdge
    dependencyEdgeCountProof :
      compositeA6DependencyEdgeCount ≡ 10
    blockers :
      List CompositeA6Blocker
    blockerCountProof :
      compositeA6BlockerCount ≡ 7
    theoremClauses :
      List A6EnstrophyLeakageRouteClause
    theoremClauseCountProof :
      a6EnstrophyLeakageRouteClauseCount ≡ 8
    decompositionClauses :
      List A6TransportCommutatorStretchingClause
    decompositionClauseCountProof :
      a6TransportCommutatorStretchingClauseCount ≡ 5
    budgetLines :
      List A6EffectiveBudgetLine
    budgetLineCountProof :
      a6EffectiveBudgetLineCount ≡ 6
    localizationChildName :
      String
    localizationChildSummary :
      String
    assembledInequalityShape :
      String
    decompositionSummary :
      String
    effectiveBudgetSummary :
      String
    dependencyDAG :
      String
    remainingBlockers :
      String
    summary :
      String
    diagonalChildTypedIsTrue :
      diagonalChildTyped ≡ true
    offDiagonalChildTypedIsTrue :
      offDiagonalChildTyped ≡ true
    llnChildTypedIsTrue :
      llnChildTyped ≡ true
    localizationChildExpectedIsTrue :
      localizationChildExpected ≡ true
    localizationChildOpenIsTrue :
      localizationChildOpen ≡ true
    localizationChildImportedIsFalse :
      localizationChildImported ≡ true
    compositeTheoremProvedIsFalse :
      compositeTheoremProved ≡ false
    a6PointwiseToAbelClosedIsFalse :
      a6PointwiseToAbelClosed ≡ false
    residualMonotonicityProvedIsFalse :
      residualMonotonicityProved ≡ false
    residualDepletionProvedIsFalse :
      residualDepletionProved ≡ false
    nsClayPromotedIsFalse :
      nsClayPromoted ≡ false
    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

canonicalNSPointwiseToAbelCompositeA6Boundary :
  NSPointwiseToAbelCompositeA6Boundary
canonicalNSPointwiseToAbelCompositeA6Boundary =
  record
    { importedSupport =
        canonicalImportedCompositeA6Support
    ; dependencyNodes =
        canonicalCompositeA6DependencyNodes
    ; dependencyNodeCountProof =
        refl
    ; dependencyEdges =
        canonicalCompositeA6DependencyEdges
    ; dependencyEdgeCountProof =
        refl
    ; blockers =
        canonicalCompositeA6Blockers
    ; blockerCountProof =
        refl
    ; theoremClauses =
        canonicalA6EnstrophyLeakageRouteClauses
    ; theoremClauseCountProof =
        refl
    ; decompositionClauses =
        canonicalA6TransportCommutatorStretchingClauses
    ; decompositionClauseCountProof =
        refl
    ; budgetLines =
        canonicalA6EffectiveBudgetLines
    ; budgetLineCountProof =
        refl
    ; localizationChildName =
        localizationChildBoundaryReference
    ; localizationChildSummary =
        localizationChildExpectedSummary
    ; assembledInequalityShape =
        a6AssembledInequalityShape
    ; decompositionSummary =
        a6TransportCommutatorStretchingSummary
    ; effectiveBudgetSummary =
        a6EffectiveBudgetSummary
    ; dependencyDAG =
        dependencyDAGSummary
    ; remainingBlockers =
        remainingBlockersSummary
    ; summary =
        orcsLpgfSummary
    ; diagonalChildTypedIsTrue =
        refl
    ; offDiagonalChildTypedIsTrue =
        refl
    ; llnChildTypedIsTrue =
        refl
    ; localizationChildExpectedIsTrue =
        refl
    ; localizationChildOpenIsTrue =
        refl
    ; localizationChildImportedIsFalse =
        refl
    ; compositeTheoremProvedIsFalse =
        refl
    ; a6PointwiseToAbelClosedIsFalse =
        refl
    ; residualMonotonicityProvedIsFalse =
        refl
    ; residualDepletionProvedIsFalse =
        refl
    ; nsClayPromotedIsFalse =
        refl
    ; terminalUnificationPromotedIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Contradictions: this composite receipt remains non-promoting.

postulate
  compositeA6BoundaryDoesNotProveA6 :
    a6PointwiseToAbelClosed ≡ true →
    ⊥

  compositeA6BoundaryDoesNotProveResidualMonotonicity :
    residualMonotonicityProved ≡ true →
    ⊥

  compositeA6BoundaryDoesNotProveNSClay :
    nsClayPromoted ≡ true →
    ⊥

  compositeA6BoundaryDoesNotProveTerminal :
    terminalUnificationPromoted ≡ true →
    ⊥
