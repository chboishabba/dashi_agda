module DASHI.Physics.Closure.UnificationCrossTermToFourPointCompositeBoundary where

-- Fail-closed composite for the sharpened U-1a integration surface.
--
-- This module records the exact dependency:
--
--   cross-term null class
--   -> quotient gluing linearity
--   -> four-point cancellation
--   -> parallelogram
--   -> quadratic emergence
--   -> terminal consumers.
--
-- It composes existing boundary/composite surfaces only.  It proves no
-- cross-term null theorem, no quotient-linearity theorem, no four-point
-- cancellation theorem, no parallelogram theorem, no quadratic emergence
-- theorem, and no terminal or Clay promotion.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.UnificationGluingCrossTermNullClassBoundary
  as CrossTerm
import DASHI.Physics.Closure.UnificationGluingLinearityCompositeBoundary
  as LinearityComposite
import DASHI.Physics.Closure.UnificationFourPointStressCompositeBoundary
  as FourPointComposite

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support bundle.

record ImportedCrossTermToFourPointSupport : Setω where
  field
    crossTermBoundary :
      CrossTerm.UnificationGluingCrossTermNullClassBoundary

    gluingLinearityComposite :
      LinearityComposite.UnificationGluingLinearityCompositeBoundary

    fourPointStressComposite :
      FourPointComposite.UnificationFourPointStressCompositeBoundary

    crossTermNullClassStillOpen :
      CrossTerm.crossTermNullClassTheoremProved crossTermBoundary ≡ false

    moduloNullLinearityStillOpen :
      CrossTerm.gluingLinearityModuloNullProved crossTermBoundary ≡ false

    crossTermFourPointStillOpen :
      CrossTerm.fourPointCancellationProved crossTermBoundary ≡ false

    crossTermParallelogramStillOpen :
      CrossTerm.parallelogramProved crossTermBoundary ≡ false

    crossTermQuadraticStillBlocked :
      CrossTerm.quadraticEmergenceProved crossTermBoundary ≡ false

    crossTermTerminalPromotionFalse :
      CrossTerm.terminalUnificationPromotion crossTermBoundary ≡ false

    crossTermClayPromotionFalse :
      CrossTerm.clayPromotion crossTermBoundary ≡ false

    linearlyCompositeGluingStillOpen :
      LinearityComposite.gluingOperatorCompatibilityTheoremProved
        gluingLinearityComposite
        ≡ false

    linearlyCompositeFourPointStillOpen :
      LinearityComposite.fourPointCancellationTheoremProved
        gluingLinearityComposite
        ≡ false

    linearlyCompositeParallelogramStillOpen :
      LinearityComposite.parallelogramTheoremProved
        gluingLinearityComposite
        ≡ false

    linearlyCompositeQuadraticStillBlocked :
      LinearityComposite.quadraticEmergenceTheoremProved
        gluingLinearityComposite
        ≡ false

    linearlyCompositePromotionFalse :
      LinearityComposite.unificationPromoted gluingLinearityComposite
        ≡ false

    fourPointCompositeLinearityStillOpen :
      FourPointComposite.gluingLinearityTheoremProved
        fourPointStressComposite
        ≡ false

    fourPointCompositeCancellationStillOpen :
      FourPointComposite.fourPointCancellationTheoremProved
        fourPointStressComposite
        ≡ false

    fourPointCompositeParallelogramStillOpen :
      FourPointComposite.parallelogramTheoremProved
        fourPointStressComposite
        ≡ false

    fourPointCompositeQuadraticStillBlocked :
      FourPointComposite.quadraticEmergenceTheoremProved
        fourPointStressComposite
        ≡ false

    fourPointCompositeTerminalPromotionFalse :
      FourPointComposite.terminalUnificationPromoted
        fourPointStressComposite
        ≡ false

open ImportedCrossTermToFourPointSupport public

canonicalImportedCrossTermToFourPointSupport :
  ImportedCrossTermToFourPointSupport
canonicalImportedCrossTermToFourPointSupport =
  record
    { crossTermBoundary =
        CrossTerm.canonicalUnificationGluingCrossTermNullClassBoundary
    ; gluingLinearityComposite =
        LinearityComposite.canonicalUnificationGluingLinearityCompositeBoundary
    ; fourPointStressComposite =
        FourPointComposite.canonicalUnificationFourPointStressCompositeBoundary
    ; crossTermNullClassStillOpen =
        CrossTerm.canonicalCrossTermNullClassTheoremStillOpen
    ; moduloNullLinearityStillOpen =
        CrossTerm.canonicalGluingLinearityModuloNullStillOpen
    ; crossTermFourPointStillOpen =
        CrossTerm.canonicalCrossTermFourPointCancellationStillOpen
    ; crossTermParallelogramStillOpen =
        CrossTerm.canonicalCrossTermParallelogramStillOpen
    ; crossTermQuadraticStillBlocked =
        CrossTerm.canonicalCrossTermQuadraticEmergenceStillBlocked
    ; crossTermTerminalPromotionFalse =
        CrossTerm.canonicalCrossTermTerminalUnificationPromotionFalse
    ; crossTermClayPromotionFalse =
        CrossTerm.canonicalCrossTermClayPromotionFalse
    ; linearlyCompositeGluingStillOpen =
        LinearityComposite.canonicalCompositeGluingCompatibilityTheoremFalse
    ; linearlyCompositeFourPointStillOpen =
        LinearityComposite.canonicalCompositeFourPointCancellationTheoremFalse
    ; linearlyCompositeParallelogramStillOpen =
        LinearityComposite.canonicalCompositeParallelogramTheoremFalse
    ; linearlyCompositeQuadraticStillBlocked =
        LinearityComposite.canonicalCompositeQuadraticEmergenceTheoremFalse
    ; linearlyCompositePromotionFalse =
        LinearityComposite.canonicalCompositeUnificationPromotionFalse
    ; fourPointCompositeLinearityStillOpen =
        FourPointComposite.canonicalFourPointStressGluingLinearityStillOpen
    ; fourPointCompositeCancellationStillOpen =
        FourPointComposite.canonicalFourPointStressCancellationStillOpen
    ; fourPointCompositeParallelogramStillOpen =
        FourPointComposite.canonicalFourPointStressParallelogramStillOpen
    ; fourPointCompositeQuadraticStillBlocked =
        FourPointComposite.canonicalFourPointStressQuadraticEmergenceStillBlocked
    ; fourPointCompositeTerminalPromotionFalse =
        FourPointComposite.canonicalFourPointStressTerminalPromotionFalse
    }

------------------------------------------------------------------------
-- Exact dependency chain.

data CrossTermToFourPointDependencyStage : Set where
  crossTermNullClassStage :
    CrossTermToFourPointDependencyStage

  quotientLinearityStage :
    CrossTermToFourPointDependencyStage

  fourPointCancellationStage :
    CrossTermToFourPointDependencyStage

  parallelogramStage :
    CrossTermToFourPointDependencyStage

  quadraticEmergenceStage :
    CrossTermToFourPointDependencyStage

  terminalConsumerStage :
    CrossTermToFourPointDependencyStage

data CrossTermToFourPointStatus : Set where
  theoremOpen :
    CrossTermToFourPointStatus

  downstreamBlocked :
    CrossTermToFourPointStatus

  promotionHeld :
    CrossTermToFourPointStatus

canonicalCrossTermToFourPointStatus :
  CrossTermToFourPointDependencyStage →
  CrossTermToFourPointStatus
canonicalCrossTermToFourPointStatus crossTermNullClassStage =
  theoremOpen
canonicalCrossTermToFourPointStatus quotientLinearityStage =
  downstreamBlocked
canonicalCrossTermToFourPointStatus fourPointCancellationStage =
  downstreamBlocked
canonicalCrossTermToFourPointStatus parallelogramStage =
  downstreamBlocked
canonicalCrossTermToFourPointStatus quadraticEmergenceStage =
  downstreamBlocked
canonicalCrossTermToFourPointStatus terminalConsumerStage =
  promotionHeld

record CrossTermToFourPointDependencyRow : Set where
  field
    stage :
      CrossTermToFourPointDependencyStage

    status :
      CrossTermToFourPointStatus

    statusIsCanonical :
      status ≡ canonicalCrossTermToFourPointStatus stage

    dependency :
      String

    importedSupport :
      String

    theoremOrPromotionProvedHere :
      Bool

    theoremOrPromotionProvedHereIsFalse :
      theoremOrPromotionProvedHere ≡ false

open CrossTermToFourPointDependencyRow public

mkDependencyRow :
  CrossTermToFourPointDependencyStage →
  String →
  String →
  CrossTermToFourPointDependencyRow
mkDependencyRow stage dependency importedSupport =
  record
    { stage =
        stage
    ; status =
        canonicalCrossTermToFourPointStatus stage
    ; statusIsCanonical =
        refl
    ; dependency =
        dependency
    ; importedSupport =
        importedSupport
    ; theoremOrPromotionProvedHere =
        false
    ; theoremOrPromotionProvedHereIsFalse =
        refl
    }

canonicalCrossTermToFourPointDependencyRows :
  List CrossTermToFourPointDependencyRow
canonicalCrossTermToFourPointDependencyRows =
  mkDependencyRow
    crossTermNullClassStage
    "prove G(s1+s2)-Gs1-Gs2 lies in the admissible quotient null class"
    "UnificationGluingCrossTermNullClassBoundary"
  ∷ mkDependencyRow
    quotientLinearityStage
    "derive quotient gluing linearity from cross-term nullity plus representative and null-class stability"
    "UnificationGluingLinearityCompositeBoundary"
  ∷ mkDependencyRow
    fourPointCancellationStage
    "consume quotient linearity to unlock gluing residual forces four-point cancellation"
    "UnificationGluingLinearityCompositeBoundary and UnificationFourPointStressCompositeBoundary"
  ∷ mkDependencyRow
    parallelogramStage
    "derive the parallelogram law only after four-point cancellation"
    "UnificationFourPointStressCompositeBoundary"
  ∷ mkDependencyRow
    quadraticEmergenceStage
    "apply Jordan-von Neumann style quadratic emergence only after parallelogram"
    "UnificationFourPointStressCompositeBoundary"
  ∷ mkDependencyRow
    terminalConsumerStage
    "hold signature, Clifford, terminal unification, and Clay consumers"
    "all imported surfaces keep promotion false"
  ∷ []

dependencyRowCount : Nat
dependencyRowCount =
  listLength canonicalCrossTermToFourPointDependencyRows

dependencyRowCountIs6 :
  dependencyRowCount ≡ 6
dependencyRowCountIs6 =
  refl

------------------------------------------------------------------------
-- Composite boundary.

record UnificationCrossTermToFourPointCompositeBoundary : Setω where
  field
    importedSupport :
      ImportedCrossTermToFourPointSupport

    dependencyRows :
      List CrossTermToFourPointDependencyRow

    dependencyRowCountField :
      Nat

    dependencyRowCountFieldIs6 :
      dependencyRowCountField ≡ 6

    dependencyRowCountMatchesRows :
      dependencyRowCountField ≡ listLength dependencyRows

    crossTermNullClassTheoremProved :
      Bool

    crossTermNullClassTheoremProvedIsFalse :
      crossTermNullClassTheoremProved ≡ false

    quotientLinearityTheoremProved :
      Bool

    quotientLinearityTheoremProvedIsFalse :
      quotientLinearityTheoremProved ≡ false

    fourPointCancellationTheoremProved :
      Bool

    fourPointCancellationTheoremProvedIsFalse :
      fourPointCancellationTheoremProved ≡ false

    parallelogramTheoremProved :
      Bool

    parallelogramTheoremProvedIsFalse :
      parallelogramTheoremProved ≡ false

    quadraticEmergenceTheoremProved :
      Bool

    quadraticEmergenceTheoremProvedIsFalse :
      quadraticEmergenceTheoremProved ≡ false

    terminalUnificationPromoted :
      Bool

    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    allTheoremPromotionFlagsFalse :
      Bool

    allTheoremPromotionFlagsFalseIsTrue :
      allTheoremPromotionFlagsFalse ≡ true

    notes :
      List String

open UnificationCrossTermToFourPointCompositeBoundary public

canonicalUnificationCrossTermToFourPointCompositeBoundary :
  UnificationCrossTermToFourPointCompositeBoundary
canonicalUnificationCrossTermToFourPointCompositeBoundary =
  record
    { importedSupport =
        canonicalImportedCrossTermToFourPointSupport
    ; dependencyRows =
        canonicalCrossTermToFourPointDependencyRows
    ; dependencyRowCountField =
        6
    ; dependencyRowCountFieldIs6 =
        refl
    ; dependencyRowCountMatchesRows =
        refl
    ; crossTermNullClassTheoremProved =
        false
    ; crossTermNullClassTheoremProvedIsFalse =
        CrossTerm.canonicalCrossTermNullClassTheoremStillOpen
    ; quotientLinearityTheoremProved =
        false
    ; quotientLinearityTheoremProvedIsFalse =
        LinearityComposite.canonicalCompositeGluingCompatibilityTheoremFalse
    ; fourPointCancellationTheoremProved =
        false
    ; fourPointCancellationTheoremProvedIsFalse =
        FourPointComposite.canonicalFourPointStressCancellationStillOpen
    ; parallelogramTheoremProved =
        false
    ; parallelogramTheoremProvedIsFalse =
        FourPointComposite.canonicalFourPointStressParallelogramStillOpen
    ; quadraticEmergenceTheoremProved =
        false
    ; quadraticEmergenceTheoremProvedIsFalse =
        FourPointComposite.canonicalFourPointStressQuadraticEmergenceStillBlocked
    ; terminalUnificationPromoted =
        false
    ; terminalUnificationPromotedIsFalse =
        FourPointComposite.canonicalFourPointStressTerminalPromotionFalse
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        FourPointComposite.canonicalFourPointStressClayPromotionFalse
    ; allTheoremPromotionFlagsFalse =
        true
    ; allTheoremPromotionFlagsFalseIsTrue =
        refl
    ; notes =
        "Exact U-1a dependency recorded: cross-term null class -> quotient linearity -> four-point cancellation -> parallelogram -> quadratic emergence."
        ∷ "Cross-term nullity is the first open theorem; quotient linearity and four-point cancellation remain downstream consumers."
        ∷ "The gluing-linearity and four-point-stress composites are imported as support, not promotion authority."
        ∷ "All theorem, terminal, and Clay promotion flags remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas for downstream consumers.

canonicalCrossTermToFourPointRowCountIs6 :
  dependencyRowCountField
    canonicalUnificationCrossTermToFourPointCompositeBoundary
  ≡ 6
canonicalCrossTermToFourPointRowCountIs6 =
  refl

canonicalCrossTermToFourPointCrossTermStillOpen :
  crossTermNullClassTheoremProved
    canonicalUnificationCrossTermToFourPointCompositeBoundary
  ≡ false
canonicalCrossTermToFourPointCrossTermStillOpen =
  CrossTerm.canonicalCrossTermNullClassTheoremStillOpen

canonicalCrossTermToFourPointQuotientLinearityStillOpen :
  quotientLinearityTheoremProved
    canonicalUnificationCrossTermToFourPointCompositeBoundary
  ≡ false
canonicalCrossTermToFourPointQuotientLinearityStillOpen =
  LinearityComposite.canonicalCompositeGluingCompatibilityTheoremFalse

canonicalCrossTermToFourPointCancellationStillOpen :
  fourPointCancellationTheoremProved
    canonicalUnificationCrossTermToFourPointCompositeBoundary
  ≡ false
canonicalCrossTermToFourPointCancellationStillOpen =
  FourPointComposite.canonicalFourPointStressCancellationStillOpen

canonicalCrossTermToFourPointParallelogramStillOpen :
  parallelogramTheoremProved
    canonicalUnificationCrossTermToFourPointCompositeBoundary
  ≡ false
canonicalCrossTermToFourPointParallelogramStillOpen =
  FourPointComposite.canonicalFourPointStressParallelogramStillOpen

canonicalCrossTermToFourPointQuadraticStillBlocked :
  quadraticEmergenceTheoremProved
    canonicalUnificationCrossTermToFourPointCompositeBoundary
  ≡ false
canonicalCrossTermToFourPointQuadraticStillBlocked =
  FourPointComposite.canonicalFourPointStressQuadraticEmergenceStillBlocked

canonicalCrossTermToFourPointTerminalPromotionFalse :
  terminalUnificationPromoted
    canonicalUnificationCrossTermToFourPointCompositeBoundary
  ≡ false
canonicalCrossTermToFourPointTerminalPromotionFalse =
  FourPointComposite.canonicalFourPointStressTerminalPromotionFalse

canonicalCrossTermToFourPointClayPromotionFalse :
  clayPromoted canonicalUnificationCrossTermToFourPointCompositeBoundary
  ≡ false
canonicalCrossTermToFourPointClayPromotionFalse =
  FourPointComposite.canonicalFourPointStressClayPromotionFalse

canonicalCrossTermToFourPointAllTheoremPromotionFlagsFalse :
  allTheoremPromotionFlagsFalse
    canonicalUnificationCrossTermToFourPointCompositeBoundary
  ≡ true
canonicalCrossTermToFourPointAllTheoremPromotionFlagsFalse =
  refl
