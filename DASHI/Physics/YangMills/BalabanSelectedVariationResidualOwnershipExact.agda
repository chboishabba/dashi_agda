module DASHI.Physics.YangMills.BalabanSelectedVariationResidualOwnershipExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- Put raw-localization and KKT-repair contributions in the same fifteen-atom
-- Boolean-cube basis before taking any upper bound.  Every atom has exactly one
-- owner.  Exact-cancellation atoms are erased before positive majorisation, and
-- the four surviving owner budgets are combined only afterwards.  This is the
-- finite no-double-payment theorem needed by the sharp singleton coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector


data ResidualOwner : Set where
  exactCancellation localizationOwner gaugeRepairOwner
    constraintRepairOwner collarBoundaryOwner : ResidualOwner

residualOwners : List ResidualOwner
residualOwners =
  exactCancellation ∷ localizationOwner ∷ gaugeRepairOwner
  ∷ constraintRepairOwner ∷ collarBoundaryOwner ∷ []

sameOwner : ResidualOwner → ResidualOwner → Bool
sameOwner exactCancellation exactCancellation = true
sameOwner localizationOwner localizationOwner = true
sameOwner gaugeRepairOwner gaugeRepairOwner = true
sameOwner constraintRepairOwner constraintRepairOwner = true
sameOwner collarBoundaryOwner collarBoundaryOwner = true
sameOwner _ _ = false

ownerSelector : ResidualOwner → ResidualOwner → ℚ
ownerSelector selected actual with sameOwner selected actual
... | true = 1ℚ
... | false = 0ℚ

record ResidualAtomFamily : Set where
  field
    rawLocalizationAtom : Cube.Subset4 → ℚ
    projectorRepairAtom : Cube.Subset4 → ℚ
    ownerOf : Cube.Subset4 → ResidualOwner

open ResidualAtomFamily public

combinedResidualAtom : ResidualAtomFamily → Cube.Subset4 → ℚ
combinedResidualAtom family subset =
  rawLocalizationAtom family subset
  - projectorRepairAtom family subset

ownedResidualAtom :
  ResidualAtomFamily → ResidualOwner → Cube.Subset4 → ℚ
ownedResidualAtom family owner subset =
  ownerSelector owner (ownerOf family subset)
  * combinedResidualAtom family subset

residualAtomReconstructedFromOwners :
  ∀ family subset →
  combinedResidualAtom family subset
  ≡ Sums.sumRational residualOwners
      (λ owner → ownedResidualAtom family owner subset)
residualAtomReconstructedFromOwners family subset
  with ownerOf family subset
... | exactCancellation =
  ℚRing.solve-∀ (combinedResidualAtom family subset)
... | localizationOwner =
  ℚRing.solve-∀ (combinedResidualAtom family subset)
... | gaugeRepairOwner =
  ℚRing.solve-∀ (combinedResidualAtom family subset)
... | constraintRepairOwner =
  ℚRing.solve-∀ (combinedResidualAtom family subset)
... | collarBoundaryOwner =
  ℚRing.solve-∀ (combinedResidualAtom family subset)

combinedResidualTotal : ResidualAtomFamily → ℚ
combinedResidualTotal family =
  Sums.sumRational Cube.nonemptySubsets4
    (combinedResidualAtom family)

ownerContribution : ResidualAtomFamily → ResidualOwner → ℚ
ownerContribution family owner =
  Sums.sumRational Cube.nonemptySubsets4
    (ownedResidualAtom family owner)

residualTotalReconstructedFromOwners : ∀ family →
  combinedResidualTotal family
  ≡ Sums.sumRational residualOwners
      (ownerContribution family)
residualTotalReconstructedFromOwners family =
  trans
    (Sums.sumRationalCong
      Cube.nonemptySubsets4
      (combinedResidualAtom family)
      (λ subset →
        Sums.sumRational residualOwners
          (λ owner → ownedResidualAtom family owner subset))
      (residualAtomReconstructedFromOwners family))
    (Fubini.sumSwap
      Cube.nonemptySubsets4
      residualOwners
      (λ subset owner → ownedResidualAtom family owner subset))

record ExactCancellationData (family : ResidualAtomFamily) : Set where
  field
    exactAtomsCancel : ∀ subset →
      ownerOf family subset ≡ exactCancellation →
      combinedResidualAtom family subset ≡ 0ℚ

open ExactCancellationData public

exactOwnerAtomZero :
  ∀ {family} →
  ExactCancellationData family →
  ∀ subset → ownedResidualAtom family exactCancellation subset ≡ 0ℚ
exactOwnerAtomZero {family} cancellation subset
  with ownerOf family subset
... | exactCancellation =
  trans
    (cong (1ℚ *_)
      (exactAtomsCancel cancellation subset refl))
    (ℚRing.solve [])
... | localizationOwner = ℚRing.solve []
... | gaugeRepairOwner = ℚRing.solve []
... | constraintRepairOwner = ℚRing.solve []
... | collarBoundaryOwner = ℚRing.solve []

exactCancellationContributionZero :
  ∀ {family} →
  ExactCancellationData family →
  ownerContribution family exactCancellation ≡ 0ℚ
exactCancellationContributionZero {family} cancellation =
  trans
    (Sums.sumRationalCong
      Cube.nonemptySubsets4
      (ownedResidualAtom family exactCancellation)
      (λ _ → 0ℚ)
      (exactOwnerAtomZero cancellation))
    (Fubini.sumRationalZero Cube.nonemptySubsets4)

survivingResidualTotal : ResidualAtomFamily → ℚ
survivingResidualTotal family =
  ownerContribution family localizationOwner
  + ownerContribution family gaugeRepairOwner
  + ownerContribution family constraintRepairOwner
  + ownerContribution family collarBoundaryOwner

exactCancellationRemovedBeforeMajorisation :
  ∀ {family} →
  ExactCancellationData family →
  combinedResidualTotal family ≡ survivingResidualTotal family
exactCancellationRemovedBeforeMajorisation {family} cancellation =
  trans
    (residualTotalReconstructedFromOwners family)
    (trans
      (cong
        (λ selected →
          selected
          + ownerContribution family localizationOwner
          + ownerContribution family gaugeRepairOwner
          + ownerContribution family constraintRepairOwner
          + ownerContribution family collarBoundaryOwner)
        (exactCancellationContributionZero cancellation))
      (ℚRing.solve-∀
        (ownerContribution family localizationOwner)
        (ownerContribution family gaugeRepairOwner)
        (ownerContribution family constraintRepairOwner)
        (ownerContribution family collarBoundaryOwner)))

record SurvivingOwnerBudgets
    (family : ResidualAtomFamily)
    (charge : ℚ) : Set where
  field
    localizationCoefficient gaugeCoefficient
      constraintCoefficient collarCoefficient : ℚ

    localizationUpper :
      ownerContribution family localizationOwner
      ≤ localizationCoefficient * charge

    gaugeUpper :
      ownerContribution family gaugeRepairOwner
      ≤ gaugeCoefficient * charge

    constraintUpper :
      ownerContribution family constraintRepairOwner
      ≤ constraintCoefficient * charge

    collarUpper :
      ownerContribution family collarBoundaryOwner
      ≤ collarCoefficient * charge

    coefficientsCloseSingletonBudget :
      localizationCoefficient + gaugeCoefficient
      + constraintCoefficient + collarCoefficient
      ≡ Selector.remainingSingletonCoefficient

open SurvivingOwnerBudgets public

survivingOwnersCloseSingletonBudget :
  ∀ {family charge} →
  SurvivingOwnerBudgets family charge →
  survivingResidualTotal family
  ≤ Selector.remainingSingletonCoefficient * charge
survivingOwnersCloseSingletonBudget {family} {charge} budgets =
  let
    firstPair = ℚP.+-mono-≤
      (localizationUpper budgets)
      (gaugeUpper budgets)

    secondPair = ℚP.+-mono-≤
      (constraintUpper budgets)
      (collarUpper budgets)

    allFour = ℚP.+-mono-≤ firstPair secondPair

    leftExact :
      (ownerContribution family localizationOwner
        + ownerContribution family gaugeRepairOwner)
      + (ownerContribution family constraintRepairOwner
        + ownerContribution family collarBoundaryOwner)
      ≡ survivingResidualTotal family
    leftExact = ℚRing.solve-∀
      (ownerContribution family localizationOwner)
      (ownerContribution family gaugeRepairOwner)
      (ownerContribution family constraintRepairOwner)
      (ownerContribution family collarBoundaryOwner)

    rightExact :
      (localizationCoefficient budgets * charge
        + gaugeCoefficient budgets * charge)
      + (constraintCoefficient budgets * charge
        + collarCoefficient budgets * charge)
      ≡ (localizationCoefficient budgets
          + gaugeCoefficient budgets
          + constraintCoefficient budgets
          + collarCoefficient budgets) * charge
    rightExact = ℚRing.solve-∀
      (localizationCoefficient budgets)
      (gaugeCoefficient budgets)
      (constraintCoefficient budgets)
      (collarCoefficient budgets)
      charge
  in
  subst
    (λ lower → lower
      ≤ Selector.remainingSingletonCoefficient * charge)
    leftExact
    (subst
      (λ upper →
        (ownerContribution family localizationOwner
          + ownerContribution family gaugeRepairOwner)
        + (ownerContribution family constraintRepairOwner
          + ownerContribution family collarBoundaryOwner)
        ≤ upper)
      (trans rightExact
        (cong (_* charge)
          (coefficientsCloseSingletonBudget budgets)))
      allFour)

ownedResidualTotalClosesSingletonBudget :
  ∀ {family charge} →
  ExactCancellationData family →
  SurvivingOwnerBudgets family charge →
  combinedResidualTotal family
  ≤ Selector.remainingSingletonCoefficient * charge
ownedResidualTotalClosesSingletonBudget cancellation budgets =
  subst
    (λ lower → lower
      ≤ Selector.remainingSingletonCoefficient * _)
    (sym (exactCancellationRemovedBeforeMajorisation cancellation))
    (survivingOwnersCloseSingletonBudget budgets)

residualOwnerPartitionLevel : ProofLevel
residualOwnerPartitionLevel = machineChecked

residualExactCancellationLevel : ProofLevel
residualExactCancellationLevel = machineChecked

residualSharpBudgetAfterCancellationLevel : ProofLevel
residualSharpBudgetAfterCancellationLevel = machineChecked
