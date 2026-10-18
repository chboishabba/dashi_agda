{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologySelectionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; proj₂)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Quantum.QuantumMereologyExact as QM
import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- PREFERRED-TPS SELECTION SURFACE
--
-- Attribution:
-- * Carroll--Singh own the external scientific proposal that quasiclassical
--   factorisations can be searched by minimizing a combination of entanglement
--   growth and internal spreading/localization criteria.
-- * DASHI owns this typed reconstruction and all generic theorems below.
-- * No source paper is attributed a DASHI existence/uniqueness theorem.
------------------------------------------------------------------------

record PreferredTPSSelectionProblem
    (W : QM.BareQuantumWorld) : Set₁ where
  field
    Candidate : Set
    realizes : Candidate → QM.TensorProductStructure W

    Admissible : Candidate → Set

    EntanglementGrowthScore : Set
    InternalSpreadingScore : Set

    entanglementGrowth :
      Candidate → EntanglementGrowthScore

    internalSpreading :
      Candidate → InternalSpreadingScore

    -- The application declares how the source-motivated objective coordinates
    -- are compared.  DASHI does not silently choose a scalarization.
    NoWorse :
      Candidate → Candidate → Set

open PreferredTPSSelectionProblem public

Optimal :
  ∀ {W} →
  (P : PreferredTPSSelectionProblem W) →
  Candidate P →
  Set
Optimal P candidate =
  Admissible P candidate
  ×
  ((other : Candidate P) →
    Admissible P other →
    NoWorse P candidate other)

record PreferredTPSSelectionReceipt
    {W : QM.BareQuantumWorld}
    (P : PreferredTPSSelectionProblem W) : Set₁ where
  field
    selected : Candidate P
    selectedOptimal : Optimal P selected

open PreferredTPSSelectionReceipt public

------------------------------------------------------------------------
-- SOURCE-OBJECTIVE REALISATION
--
-- Carroll--Singh own the external proposal to minimize a combination of the
-- two quasiclassical coordinates.  The application supplies the actual
-- combined carrier/order and proves it agrees with the generic NoWorse
-- relation.  DASHI then owns the transport theorem below.
------------------------------------------------------------------------

record CarrollSinghObjectiveRealization
    {W : QM.BareQuantumWorld}
    (P : PreferredTPSSelectionProblem W) : Set₁ where
  field
    CombinedObjective : Set

    combine :
      EntanglementGrowthScore P →
      InternalSpreadingScore P →
      CombinedObjective

    ObjectiveNoWorse :
      CombinedObjective → CombinedObjective → Set

    noWorseToCombined :
      ∀ left right →
      NoWorse P left right →
      ObjectiveNoWorse
        (combine
          (entanglementGrowth P left)
          (internalSpreading P left))
        (combine
          (entanglementGrowth P right)
          (internalSpreading P right))

    combinedToNoWorse :
      ∀ left right →
      ObjectiveNoWorse
        (combine
          (entanglementGrowth P left)
          (internalSpreading P left))
        (combine
          (entanglementGrowth P right)
          (internalSpreading P right)) →
      NoWorse P left right

open CarrollSinghObjectiveRealization public

selectionReceiptMinimizesRealizedCombinedObjective :
  ∀ {W}
    {P : PreferredTPSSelectionProblem W} →
  (objective : CarrollSinghObjectiveRealization P) →
  (receipt : PreferredTPSSelectionReceipt P) →
  (other : Candidate P) →
  Admissible P other →
  ObjectiveNoWorse objective
    (combine objective
      (entanglementGrowth P (selected receipt))
      (internalSpreading P (selected receipt)))
    (combine objective
      (entanglementGrowth P other)
      (internalSpreading P other))
selectionReceiptMinimizesRealizedCombinedObjective
    objective receipt other otherAdmissible =
  noWorseToCombined
    objective
    (selected receipt)
    other
    ((proj₂ (selectedOptimal receipt))
      other
      otherAdmissible)

------------------------------------------------------------------------
-- Uniqueness is a separate authority.
------------------------------------------------------------------------

record UniquePreferredTPSAuthority
    {W : QM.BareQuantumWorld}
    (P : PreferredTPSSelectionProblem W) : Set₁ where
  field
    SameTPS :
      Candidate P → Candidate P → Set

    optimalCandidatesAgree :
      ∀ left right →
      Optimal P left →
      Optimal P right →
      SameTPS left right

open UniquePreferredTPSAuthority public

twoOptimalSelectionsAgreeGivenUniqueness :
  ∀ {W}
    {P : PreferredTPSSelectionProblem W} →
  (authority : UniquePreferredTPSAuthority P) →
  (left right : PreferredTPSSelectionReceipt P) →
  SameTPS authority (selected left) (selected right)
twoOptimalSelectionsAgreeGivenUniqueness authority left right =
  optimalCandidatesAgree
    authority
    (selected left)
    (selected right)
    (selectedOptimal left)
    (selectedOptimal right)

------------------------------------------------------------------------
-- CRITERION OBSERVATION / CONSUMER SUFFICIENCY
--
-- A preferred-TPS criterion can be an observer on candidate space.  Existing
-- DASHI consumer-descent machinery then decides whether that observer retains
-- enough information for a declared downstream consumer.
------------------------------------------------------------------------

record CriterionConsumerSurface
    {W : QM.BareQuantumWorld}
    (P : PreferredTPSSelectionProblem W) : Set₁ where
  field
    Surface Outcome : Set

    observeCriterion :
      Candidate P → Surface

    consumer :
      Candidate P → Outcome

open CriterionConsumerSurface public

CriterionConsumerSufficient :
  ∀ {W}
    {P : PreferredTPSSelectionProblem W} →
  (S : CriterionConsumerSurface P) →
  Set
CriterionConsumerSufficient S =
  Descent.ConsumerSufficient
    (observeCriterion S)
    (consumer S)

record CriterionCollision
    {W : QM.BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    (S : CriterionConsumerSurface P) : Set where
  field
    witness :
      Descent.ConsumerNonDescentWitness
        (observeCriterion S)
        (consumer S)

open CriterionCollision public

criterionCollisionBlocksConsumerSufficiency :
  ∀ {W}
    {P : PreferredTPSSelectionProblem W}
    {S : CriterionConsumerSurface P} →
  CriterionCollision S →
  CriterionConsumerSufficient S →
  ⊥
criterionCollisionBlocksConsumerSufficiency collision =
  Descent.nonDescentWitnessBlocksSufficiency
    (witness collision)

criterionCollisionBlocksFactorization :
  ∀ {W}
    {P : PreferredTPSSelectionProblem W}
    {S : CriterionConsumerSurface P} →
  CriterionCollision S →
  Descent.FactorsThrough
    (observeCriterion S)
    (consumer S) →
  ⊥
criterionCollisionBlocksFactorization collision =
  Descent.nonDescentWitnessBlocksFactorization
    (witness collision)

criterionCollisionForcesSeparationInEveryRepair :
  ∀ {W}
    {P : PreferredTPSSelectionProblem W}
    {S : CriterionConsumerSurface P}
    {Refinement : Set}
    {refine : Candidate P → Refinement} →
  (collision : CriterionCollision S) →
  Repair.RefinementRepairs
    (observeCriterion S)
    refine
    (consumer S) →
  refine (Descent.left (witness collision))
    ≡
    refine (Descent.right (witness collision)) →
  ⊥
criterionCollisionForcesSeparationInEveryRepair collision =
  Repair.refinementRepairSeparatesWitness
    (witness collision)

------------------------------------------------------------------------
-- FAIL-CLOSED STATUS
------------------------------------------------------------------------

record PreferredTPSSelectionBoundary : Set where
  field
    sourceObjectiveCreatesLocalMinimizer : Bool
    sourceObjectiveCreatesLocalMinimizerIsFalse :
      sourceObjectiveCreatesLocalMinimizer ≡ false

    oneOptimalReceiptCreatesUniqueness : Bool
    oneOptimalReceiptCreatesUniquenessIsFalse :
      oneOptimalReceiptCreatesUniqueness ≡ false

    scalarizationChosenByDASHIWithoutApplication : Bool
    scalarizationChosenByDASHIWithoutApplicationIsFalse :
      scalarizationChosenByDASHIWithoutApplication ≡ false

    criterionAdequacyIsConsumerRelative : Bool
    criterionAdequacyIsConsumerRelativeIsTrue :
      criterionAdequacyIsConsumerRelative ≡ true

    criterionCollisionCreatesRefinementObligation : Bool
    criterionCollisionCreatesRefinementObligationIsTrue :
      criterionCollisionCreatesRefinementObligation ≡ true

canonicalPreferredTPSSelectionBoundary :
  PreferredTPSSelectionBoundary
canonicalPreferredTPSSelectionBoundary = record
  { sourceObjectiveCreatesLocalMinimizer = false
  ; sourceObjectiveCreatesLocalMinimizerIsFalse = refl
  ; oneOptimalReceiptCreatesUniqueness = false
  ; oneOptimalReceiptCreatesUniquenessIsFalse = refl
  ; scalarizationChosenByDASHIWithoutApplication = false
  ; scalarizationChosenByDASHIWithoutApplicationIsFalse = refl
  ; criterionAdequacyIsConsumerRelative = true
  ; criterionAdequacyIsConsumerRelativeIsTrue = refl
  ; criterionCollisionCreatesRefinementObligation = true
  ; criterionCollisionCreatesRefinementObligationIsTrue = refl
  }
