module DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact where

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
-- Put raw localization and the two-source multiplier Green contraction into
-- one nonempty-subset basis.  The public sign is the Round-40 canonical sign
--
--   projected spillover
--     = sum_S raw_S - sum_(S,T) green_(S,T).
--
-- Each Green pair owns an orbit tag, orientation tag and collar displacement.
-- Signed contributions are aggregated by owner before any upper bound is
-- applied.  The exact-cancellation fibre is then removed definitionally and
-- only the four surviving owner totals are taxed against 55/18874368.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector

data CorrelatedResidualOwner : Set where
  exactCancellation localizationOwner transportOwner
    nearGreenOwner farGreenOwner : CorrelatedResidualOwner

correlatedResidualOwners : List CorrelatedResidualOwner
correlatedResidualOwners =
  exactCancellation ∷ localizationOwner ∷ transportOwner
  ∷ nearGreenOwner ∷ farGreenOwner ∷ []

sameOwner : CorrelatedResidualOwner → CorrelatedResidualOwner → Bool
sameOwner exactCancellation exactCancellation = true
sameOwner localizationOwner localizationOwner = true
sameOwner transportOwner transportOwner = true
sameOwner nearGreenOwner nearGreenOwner = true
sameOwner farGreenOwner farGreenOwner = true
sameOwner _ _ = false

ownerSelector : CorrelatedResidualOwner → CorrelatedResidualOwner → ℚ
ownerSelector selected actual with sameOwner selected actual
... | true = 1ℚ
... | false = 0ℚ

record WilsonConstraintSourceAtom : Set where
  constructor sourceAtom
  field sourceSubset : Cube.Subset4
open WilsonConstraintSourceAtom public

record RawExtractorConstraintAtom : Set where
  constructor defectAtom
  field defectSubset : Cube.Subset4
open RawExtractorConstraintAtom public

record MultiplierGreenAtomPair : Set where
  constructor greenPair
  field
    source : WilsonConstraintSourceAtom
    defect : RawExtractorConstraintAtom
open MultiplierGreenAtomPair public

record MultiplierGreenAtomOwner : Set where
  constructor greenOwner
  field
    ownerClass : CorrelatedResidualOwner
    orbitTag : Nat
    orientationReversing : Bool
    collarDisplacement : Nat
open MultiplierGreenAtomOwner public

record CorrelatedResidualFamily : Set₁ where
  field
    rawLocalizationAtom : Cube.Subset4 → ℚ
    multiplierGreenAtom : Cube.Subset4 → Cube.Subset4 → ℚ
    rawOwnerOf : Cube.Subset4 → CorrelatedResidualOwner
    greenOwnerOf :
      Cube.Subset4 → Cube.Subset4 → MultiplierGreenAtomOwner
open CorrelatedResidualFamily public

selectedRawAtom :
  CorrelatedResidualFamily → CorrelatedResidualOwner → Cube.Subset4 → ℚ
selectedRawAtom family owner subset =
  ownerSelector owner (rawOwnerOf family subset)
  * rawLocalizationAtom family subset

selectedGreenAtom :
  CorrelatedResidualFamily → CorrelatedResidualOwner →
  Cube.Subset4 → Cube.Subset4 → ℚ
selectedGreenAtom family owner left right =
  ownerSelector owner
    (ownerClass (greenOwnerOf family left right))
  * multiplierGreenAtom family left right

rawLocalizationTotal : CorrelatedResidualFamily → ℚ
rawLocalizationTotal family =
  Sums.sumRational Cube.nonemptySubsets4
    (rawLocalizationAtom family)

greenPairTotal : CorrelatedResidualFamily → ℚ
greenPairTotal family =
  Sums.sumRational Cube.nonemptySubsets4
    (λ left →
      Sums.sumRational Cube.nonemptySubsets4
        (multiplierGreenAtom family left))

correlatedResidualTotal : CorrelatedResidualFamily → ℚ
correlatedResidualTotal family =
  rawLocalizationTotal family - greenPairTotal family

rawOwnerTotal :
  CorrelatedResidualFamily → CorrelatedResidualOwner → ℚ
rawOwnerTotal family owner =
  Sums.sumRational Cube.nonemptySubsets4
    (selectedRawAtom family owner)

greenOwnerTotal :
  CorrelatedResidualFamily → CorrelatedResidualOwner → ℚ
greenOwnerTotal family owner =
  Sums.sumRational Cube.nonemptySubsets4
    (λ left →
      Sums.sumRational Cube.nonemptySubsets4
        (selectedGreenAtom family owner left))

ownerContribution :
  CorrelatedResidualFamily → CorrelatedResidualOwner → ℚ
ownerContribution family owner =
  rawOwnerTotal family owner - greenOwnerTotal family owner

rawAtomReconstructedFromOwners : ∀ family subset →
  rawLocalizationAtom family subset
  ≡ Sums.sumRational correlatedResidualOwners
      (λ owner → selectedRawAtom family owner subset)
rawAtomReconstructedFromOwners family subset
  with rawOwnerOf family subset
... | exactCancellation = ℚRing.solve-∀ (rawLocalizationAtom family subset)
... | localizationOwner = ℚRing.solve-∀ (rawLocalizationAtom family subset)
... | transportOwner = ℚRing.solve-∀ (rawLocalizationAtom family subset)
... | nearGreenOwner = ℚRing.solve-∀ (rawLocalizationAtom family subset)
... | farGreenOwner = ℚRing.solve-∀ (rawLocalizationAtom family subset)

greenAtomReconstructedFromOwners : ∀ family left right →
  multiplierGreenAtom family left right
  ≡ Sums.sumRational correlatedResidualOwners
      (λ owner → selectedGreenAtom family owner left right)
greenAtomReconstructedFromOwners family left right
  with ownerClass (greenOwnerOf family left right)
... | exactCancellation = ℚRing.solve-∀ (multiplierGreenAtom family left right)
... | localizationOwner = ℚRing.solve-∀ (multiplierGreenAtom family left right)
... | transportOwner = ℚRing.solve-∀ (multiplierGreenAtom family left right)
... | nearGreenOwner = ℚRing.solve-∀ (multiplierGreenAtom family left right)
... | farGreenOwner = ℚRing.solve-∀ (multiplierGreenAtom family left right)

rawTotalReconstructedFromOwners : ∀ family →
  rawLocalizationTotal family
  ≡ Sums.sumRational correlatedResidualOwners
      (rawOwnerTotal family)
rawTotalReconstructedFromOwners family =
  trans
    (Sums.sumRationalCong
      Cube.nonemptySubsets4
      (rawLocalizationAtom family)
      (λ subset →
        Sums.sumRational correlatedResidualOwners
          (λ owner → selectedRawAtom family owner subset))
      (rawAtomReconstructedFromOwners family))
    (Fubini.sumSwap
      Cube.nonemptySubsets4 correlatedResidualOwners
      (λ subset owner → selectedRawAtom family owner subset))

greenAtLeftReconstructedFromOwners : ∀ family left →
  Sums.sumRational Cube.nonemptySubsets4
    (multiplierGreenAtom family left)
  ≡ Sums.sumRational correlatedResidualOwners
      (λ owner →
        Sums.sumRational Cube.nonemptySubsets4
          (selectedGreenAtom family owner left))
greenAtLeftReconstructedFromOwners family left =
  trans
    (Sums.sumRationalCong
      Cube.nonemptySubsets4
      (multiplierGreenAtom family left)
      (λ right →
        Sums.sumRational correlatedResidualOwners
          (λ owner → selectedGreenAtom family owner left right))
      (greenAtomReconstructedFromOwners family left))
    (Fubini.sumSwap
      Cube.nonemptySubsets4 correlatedResidualOwners
      (λ right owner → selectedGreenAtom family owner left right))

greenTotalReconstructedFromOwners : ∀ family →
  greenPairTotal family
  ≡ Sums.sumRational correlatedResidualOwners
      (greenOwnerTotal family)
greenTotalReconstructedFromOwners family =
  trans
    (Sums.sumRationalCong
      Cube.nonemptySubsets4
      (λ left →
        Sums.sumRational Cube.nonemptySubsets4
          (multiplierGreenAtom family left))
      (λ left →
        Sums.sumRational correlatedResidualOwners
          (λ owner →
            Sums.sumRational Cube.nonemptySubsets4
              (selectedGreenAtom family owner left)))
      (greenAtLeftReconstructedFromOwners family))
    (Fubini.sumSwap
      Cube.nonemptySubsets4 correlatedResidualOwners
      (λ left owner →
        Sums.sumRational Cube.nonemptySubsets4
          (selectedGreenAtom family owner left)))

correlatedResidualReconstructedFromOwners : ∀ family →
  correlatedResidualTotal family
  ≡ Sums.sumRational correlatedResidualOwners
      (ownerContribution family)
correlatedResidualReconstructedFromOwners family =
  let
    rawExpanded = rawTotalReconstructedFromOwners family
    greenExpanded = greenTotalReconstructedFromOwners family
    negatedGreen = Rect.sumRationalNegate
      correlatedResidualOwners (greenOwnerTotal family)
    ownerExpanded = Fubini.sumRationalAdd
      correlatedResidualOwners
      (rawOwnerTotal family)
      (λ owner → - greenOwnerTotal family owner)
  in
  trans
    (cong₂ _-_ rawExpanded greenExpanded)
    (trans
      (ℚRing.solve-∀
        (Sums.sumRational correlatedResidualOwners (rawOwnerTotal family))
        (Sums.sumRational correlatedResidualOwners (greenOwnerTotal family)))
      (trans
        (cong
          (λ selected →
            Sums.sumRational correlatedResidualOwners (rawOwnerTotal family)
            + selected)
          (sym negatedGreen))
        (sym ownerExpanded)))

record ExactCorrelatedCancellation
    (family : CorrelatedResidualFamily) : Set where
  field
    exactOwnerCancels :
      ownerContribution family exactCancellation ≡ 0ℚ
open ExactCorrelatedCancellation public

survivingCorrelatedResidual : CorrelatedResidualFamily → ℚ
survivingCorrelatedResidual family =
  ownerContribution family localizationOwner
  + ownerContribution family transportOwner
  + ownerContribution family nearGreenOwner
  + ownerContribution family farGreenOwner

exactCorrelatedCancellationRemovedBeforeMajorisation :
  ∀ {family} →
  ExactCorrelatedCancellation family →
  correlatedResidualTotal family
  ≡ survivingCorrelatedResidual family
exactCorrelatedCancellationRemovedBeforeMajorisation {family} cancellation =
  trans
    (correlatedResidualReconstructedFromOwners family)
    (trans
      (cong
        (λ selected →
          selected
          + ownerContribution family localizationOwner
          + ownerContribution family transportOwner
          + ownerContribution family nearGreenOwner
          + ownerContribution family farGreenOwner)
        (exactOwnerCancels cancellation))
      (ℚRing.solve-∀
        (ownerContribution family localizationOwner)
        (ownerContribution family transportOwner)
        (ownerContribution family nearGreenOwner)
        (ownerContribution family farGreenOwner)))

record CorrelatedOwnerBudgets
    (family : CorrelatedResidualFamily)
    (charge : ℚ) : Set where
  field
    localizationCoefficient transportCoefficient
      nearGreenCoefficient farGreenCoefficient : ℚ

    localizationUpper :
      ownerContribution family localizationOwner
      ≤ localizationCoefficient * charge
    transportUpper :
      ownerContribution family transportOwner
      ≤ transportCoefficient * charge
    nearGreenUpper :
      ownerContribution family nearGreenOwner
      ≤ nearGreenCoefficient * charge
    farGreenUpper :
      ownerContribution family farGreenOwner
      ≤ farGreenCoefficient * charge

    coefficientsCloseSingletonBudget :
      localizationCoefficient + transportCoefficient
      + nearGreenCoefficient + farGreenCoefficient
      ≡ Selector.remainingSingletonCoefficient
open CorrelatedOwnerBudgets public

correlatedOwnersCloseSingletonBudget :
  ∀ {family charge} →
  CorrelatedOwnerBudgets family charge →
  survivingCorrelatedResidual family
  ≤ Selector.remainingSingletonCoefficient * charge
correlatedOwnersCloseSingletonBudget {family} {charge} budgets =
  let
    firstPair = ℚP.+-mono-≤
      (localizationUpper budgets) (transportUpper budgets)
    secondPair = ℚP.+-mono-≤
      (nearGreenUpper budgets) (farGreenUpper budgets)
    allFour = ℚP.+-mono-≤ firstPair secondPair
    lowerExact = ℚRing.solve-∀
      (ownerContribution family localizationOwner)
      (ownerContribution family transportOwner)
      (ownerContribution family nearGreenOwner)
      (ownerContribution family farGreenOwner)
    upperExact = trans
      (ℚRing.solve-∀
        (localizationCoefficient budgets)
        (transportCoefficient budgets)
        (nearGreenCoefficient budgets)
        (farGreenCoefficient budgets) charge)
      (cong (_* charge)
        (coefficientsCloseSingletonBudget budgets))
  in
  subst
    (λ lower → lower
      ≤ Selector.remainingSingletonCoefficient * charge)
    lowerExact
    (subst
      (λ upper →
        (ownerContribution family localizationOwner
          + ownerContribution family transportOwner)
        + (ownerContribution family nearGreenOwner
          + ownerContribution family farGreenOwner)
        ≤ upper)
      upperExact allFour)

correlatedResidualClosesSingletonBudget :
  ∀ {family charge} →
  ExactCorrelatedCancellation family →
  CorrelatedOwnerBudgets family charge →
  correlatedResidualTotal family
  ≤ Selector.remainingSingletonCoefficient * charge
correlatedResidualClosesSingletonBudget cancellation budgets =
  subst
    (λ lower → lower
      ≤ Selector.remainingSingletonCoefficient * _)
    (sym
      (exactCorrelatedCancellationRemovedBeforeMajorisation cancellation))
    (correlatedOwnersCloseSingletonBudget budgets)

correlatedResidualPairOwnershipLevel : ProofLevel
correlatedResidualPairOwnershipLevel = machineChecked

correlatedResidualDelayedMajorisationLevel : ProofLevel
correlatedResidualDelayedMajorisationLevel = machineChecked

selectedCorrelatedResidualPhysicalBudgetProducerLevel : ProofLevel
selectedCorrelatedResidualPhysicalBudgetProducerLevel = conditional
