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
-- Put all three selected-variation objects into one nonempty-subset basis:
-- raw localization r_S, the constraint source s_S and the extractor defect
-- delta_T.  The Green contribution is indexed by a pair (S,T), while raw
-- localization remains singly indexed.  Both are assigned to one common owner
-- before any positive majorisation:
--
--   R = - sum_S r_S + sum_(S,T) <s_S,K+ delta_T>.
--
-- The module proves exact reconstruction from owner fibres, removes the exact
-- cancellation fibre before taxation, and transports four symbolic owner
-- bounds into the literal 55/18874368 singleton budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

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
  field
    sourceSubset : Cube.Subset4

record RawExtractorConstraintAtom : Set where
  constructor defectAtom
  field
    defectSubset : Cube.Subset4

record MultiplierGreenAtomPair : Set where
  constructor greenPair
  field
    source : WilsonConstraintSourceAtom
    defect : RawExtractorConstraintAtom

record CorrelatedResidualFamily : Set where
  field
    rawLocalizationAtom : Cube.Subset4 → ℚ
    multiplierGreenAtom : Cube.Subset4 → Cube.Subset4 → ℚ
    rawOwnerOf : Cube.Subset4 → CorrelatedResidualOwner
    greenOwnerOf :
      Cube.Subset4 → Cube.Subset4 → CorrelatedResidualOwner

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
  ownerSelector owner (greenOwnerOf family left right)
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
  - rawLocalizationTotal family + greenPairTotal family

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
  - rawOwnerTotal family owner + greenOwnerTotal family owner

rawAtomReconstructedFromOwners : ∀ family subset →
  rawLocalizationAtom family subset
  ≡ Sums.sumRational correlatedResidualOwners
      (λ owner → selectedRawAtom family owner subset)
rawAtomReconstructedFromOwners family subset
  with rawOwnerOf family subset
... | exactCancellation =
  ℚRing.solve-∀ (rawLocalizationAtom family subset)
... | localizationOwner =
  ℚRing.solve-∀ (rawLocalizationAtom family subset)
... | transportOwner =
  ℚRing.solve-∀ (rawLocalizationAtom family subset)
... | nearGreenOwner =
  ℚRing.solve-∀ (rawLocalizationAtom family subset)
... | farGreenOwner =
  ℚRing.solve-∀ (rawLocalizationAtom family subset)

greenAtomReconstructedFromOwners : ∀ family left right →
  multiplierGreenAtom family left right
  ≡ Sums.sumRational correlatedResidualOwners
      (λ owner → selectedGreenAtom family owner left right)
greenAtomReconstructedFromOwners family left right
  with greenOwnerOf family left right
... | exactCancellation =
  ℚRing.solve-∀ (multiplierGreenAtom family left right)
... | localizationOwner =
  ℚRing.solve-∀ (multiplierGreenAtom family left right)
... | transportOwner =
  ℚRing.solve-∀ (multiplierGreenAtom family left right)
... | nearGreenOwner =
  ℚRing.solve-∀ (multiplierGreenAtom family left right)
... | farGreenOwner =
  ℚRing.solve-∀ (multiplierGreenAtom family left right)

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
      Cube.nonemptySubsets4
      correlatedResidualOwners
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
      Cube.nonemptySubsets4
      correlatedResidualOwners
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
      Cube.nonemptySubsets4
      correlatedResidualOwners
      (λ left owner →
        Sums.sumRational Cube.nonemptySubsets4
          (selectedGreenAtom family owner left)))

correlatedResidualReconstructedFromOwners : ∀ family →
  correlatedResidualTotal family
  ≡ Sums.sumRational correlatedResidualOwners
      (ownerContribution family)
correlatedResidualReconstructedFromOwners family =
  let
    ownerExpansion =
      Fubini.sumRationalAdd
        correlatedResidualOwners
        (λ owner → - rawOwnerTotal family owner)
        (greenOwnerTotal family)

    rawNegation =
      Rect.sumRationalNegate
        correlatedResidualOwners
        (rawOwnerTotal family)
  in
  trans
    (cong₂ _+_
      (cong -_ (rawTotalReconstructedFromOwners family))
      (greenTotalReconstructedFromOwners family))
    (trans
      (cong
        (λ selected → selected
          + Sums.sumRational correlatedResidualOwners
              (greenOwnerTotal family))
        (sym rawNegation))
      (sym ownerExpansion))

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

exactCorrelatedCancellationRemovedBeforeTaxation :
  ∀ {family} →
  ExactCorrelatedCancellation family →
  correlatedResidualTotal family
  ≡ survivingCorrelatedResidual family
exactCorrelatedCancellationRemovedBeforeTaxation
    {family} cancellation =
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
      (localizationUpper budgets)
      (transportUpper budgets)
    secondPair = ℚP.+-mono-≤
      (nearGreenUpper budgets)
      (farGreenUpper budgets)
    allFour = ℚP.+-mono-≤ firstPair secondPair

    leftExact :
      (ownerContribution family localizationOwner
        + ownerContribution family transportOwner)
      + (ownerContribution family nearGreenOwner
        + ownerContribution family farGreenOwner)
      ≡ survivingCorrelatedResidual family
    leftExact = ℚRing.solve-∀
      (ownerContribution family localizationOwner)
      (ownerContribution family transportOwner)
      (ownerContribution family nearGreenOwner)
      (ownerContribution family farGreenOwner)

    rightExact :
      (localizationCoefficient budgets * charge
        + transportCoefficient budgets * charge)
      + (nearGreenCoefficient budgets * charge
        + farGreenCoefficient budgets * charge)
      ≡ (localizationCoefficient budgets
          + transportCoefficient budgets
          + nearGreenCoefficient budgets
          + farGreenCoefficient budgets) * charge
    rightExact = ℚRing.solve-∀
      (localizationCoefficient budgets)
      (transportCoefficient budgets)
      (nearGreenCoefficient budgets)
      (farGreenCoefficient budgets)
      charge
  in
  subst
    (λ lower → lower
      ≤ Selector.remainingSingletonCoefficient * charge)
    leftExact
    (subst
      (λ upper →
        (ownerContribution family localizationOwner
          + ownerContribution family transportOwner)
        + (ownerContribution family nearGreenOwner
          + ownerContribution family farGreenOwner)
        ≤ upper)
      (trans rightExact
        (cong (_* charge)
          (coefficientsCloseSingletonBudget budgets)))
      allFour)

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
      (exactCorrelatedCancellationRemovedBeforeTaxation cancellation))
    (correlatedOwnersCloseSingletonBudget budgets)

correlatedResidualPairOwnershipLevel : ProofLevel
correlatedResidualPairOwnershipLevel = machineChecked

correlatedResidualDelayedTaxationLevel : ProofLevel
correlatedResidualDelayedTaxationLevel = machineChecked

selectedCorrelatedResidualPhysicalBudgetProducerLevel : ProofLevel
selectedCorrelatedResidualPhysicalBudgetProducerLevel = conditional
