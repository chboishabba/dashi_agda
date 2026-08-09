module DASHI.Physics.YangMills.BalabanSelectedCorrelatedGreenAtomOwnershipExact where

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
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Expand the canonical residual
--
--   RawLocalization - <Lg,K+ Lw>
--
-- in one Boolean-cube basis.  The Green term is indexed by a pair (S,T) of
-- nonempty subsets, not by one atom.  Every pair retains its D4 orbit label,
-- orientation and collar displacement.  Signed terms are first aggregated by
-- owner; only the surviving owner totals may be positively majorised.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanWilsonD4SubsetCharacterExact as D4

record WilsonConstraintSourceAtom : Set where
  constructor sourceAtom
  field sourceSubset : Cube.Subset4
open WilsonConstraintSourceAtom public

record RawExtractorConstraintAtom : Set where
  constructor defectAtom
  field defectSubset : Cube.Subset4
open RawExtractorConstraintAtom public

record MultiplierGreenAtomPair : Set where
  constructor greenAtomPair
  field
    source : WilsonConstraintSourceAtom
    defect : RawExtractorConstraintAtom
open MultiplierGreenAtomPair public

data GreenOrientation : Set where
  orientationPreserving orientationReversing : GreenOrientation

data CorrelatedResidualOwner : Set where
  exactCancellationOwner rawLocalizationOwner multiplierGreenOwner
    collarDisplacementOwner transportCorrectionOwner : CorrelatedResidualOwner

correlatedResidualOwners : List CorrelatedResidualOwner
correlatedResidualOwners =
  exactCancellationOwner ∷ rawLocalizationOwner ∷ multiplierGreenOwner
  ∷ collarDisplacementOwner ∷ transportCorrectionOwner ∷ []

sameOwner : CorrelatedResidualOwner → CorrelatedResidualOwner → Bool
sameOwner exactCancellationOwner exactCancellationOwner = true
sameOwner rawLocalizationOwner rawLocalizationOwner = true
sameOwner multiplierGreenOwner multiplierGreenOwner = true
sameOwner collarDisplacementOwner collarDisplacementOwner = true
sameOwner transportCorrectionOwner transportCorrectionOwner = true
sameOwner _ _ = false

ownerSelector : CorrelatedResidualOwner → CorrelatedResidualOwner → ℚ
ownerSelector selected actual with sameOwner selected actual
... | true = 1ℚ
... | false = 0ℚ

record MultiplierGreenAtomOwner : Set where
  constructor greenOwner
  field
    ownerClass : CorrelatedResidualOwner
    orbitRepresentative : D4.SlotPermutation4
    orientation : GreenOrientation
    collarDisplacement : Nat
open MultiplierGreenAtomOwner public

record CorrelatedGreenAtomFamily : Set₁ where
  field
    rawLocalizationAtom : Cube.Subset4 → ℚ
    constraintSourceAtom : Cube.Subset4 → ℚ
    rawConstraintDefectAtom : Cube.Subset4 → ℚ
    greenPairAtom : Cube.Subset4 → Cube.Subset4 → ℚ

    rawOwner : Cube.Subset4 → CorrelatedResidualOwner
    pairOwner : Cube.Subset4 → Cube.Subset4 → MultiplierGreenAtomOwner

    sourceReconstructed :
      Sums.sumRational Cube.nonemptySubsets4 constraintSourceAtom
      ≡ Sums.sumRational Cube.nonemptySubsets4 constraintSourceAtom

    defectReconstructed :
      Sums.sumRational Cube.nonemptySubsets4 rawConstraintDefectAtom
      ≡ Sums.sumRational Cube.nonemptySubsets4 rawConstraintDefectAtom

open CorrelatedGreenAtomFamily public

rawLocalizationTotal : CorrelatedGreenAtomFamily → ℚ
rawLocalizationTotal family =
  Sums.sumRational Cube.nonemptySubsets4
    (rawLocalizationAtom family)

greenContractionTotal : CorrelatedGreenAtomFamily → ℚ
greenContractionTotal family =
  Sums.sumRational Cube.nonemptySubsets4
    (λ sourceSubsetValue →
      Sums.sumRational Cube.nonemptySubsets4
        (greenPairAtom family sourceSubsetValue))

correlatedResidualTotal : CorrelatedGreenAtomFamily → ℚ
correlatedResidualTotal family =
  rawLocalizationTotal family - greenContractionTotal family

ownedRawAtom :
  CorrelatedGreenAtomFamily → CorrelatedResidualOwner → Cube.Subset4 → ℚ
ownedRawAtom family owner subset =
  ownerSelector owner (rawOwner family subset)
  * rawLocalizationAtom family subset

ownedGreenPairAtom :
  CorrelatedGreenAtomFamily → CorrelatedResidualOwner →
  Cube.Subset4 → Cube.Subset4 → ℚ
ownedGreenPairAtom family owner sourceSubsetValue defectSubsetValue =
  ownerSelector owner
    (ownerClass (pairOwner family sourceSubsetValue defectSubsetValue))
  * (- greenPairAtom family sourceSubsetValue defectSubsetValue)

ownerContribution :
  CorrelatedGreenAtomFamily → CorrelatedResidualOwner → ℚ
ownerContribution family owner =
  Sums.sumRational Cube.nonemptySubsets4
    (ownedRawAtom family owner)
  + Sums.sumRational Cube.nonemptySubsets4
      (λ sourceSubsetValue →
        Sums.sumRational Cube.nonemptySubsets4
          (ownedGreenPairAtom family owner sourceSubsetValue))

rawAtomReconstructedFromOwners : ∀ family subset →
  rawLocalizationAtom family subset
  ≡ Sums.sumRational correlatedResidualOwners
      (λ owner → ownedRawAtom family owner subset)
rawAtomReconstructedFromOwners family subset
  with rawOwner family subset
... | exactCancellationOwner = ℚRing.solve-∀ (rawLocalizationAtom family subset)
... | rawLocalizationOwner = ℚRing.solve-∀ (rawLocalizationAtom family subset)
... | multiplierGreenOwner = ℚRing.solve-∀ (rawLocalizationAtom family subset)
... | collarDisplacementOwner = ℚRing.solve-∀ (rawLocalizationAtom family subset)
... | transportCorrectionOwner = ℚRing.solve-∀ (rawLocalizationAtom family subset)

greenPairReconstructedFromOwners : ∀ family sourceSubsetValue defectSubsetValue →
  - greenPairAtom family sourceSubsetValue defectSubsetValue
  ≡ Sums.sumRational correlatedResidualOwners
      (λ owner → ownedGreenPairAtom family owner
        sourceSubsetValue defectSubsetValue)
greenPairReconstructedFromOwners family sourceSubsetValue defectSubsetValue
  with ownerClass (pairOwner family sourceSubsetValue defectSubsetValue)
... | exactCancellationOwner =
  ℚRing.solve-∀ (greenPairAtom family sourceSubsetValue defectSubsetValue)
... | rawLocalizationOwner =
  ℚRing.solve-∀ (greenPairAtom family sourceSubsetValue defectSubsetValue)
... | multiplierGreenOwner =
  ℚRing.solve-∀ (greenPairAtom family sourceSubsetValue defectSubsetValue)
... | collarDisplacementOwner =
  ℚRing.solve-∀ (greenPairAtom family sourceSubsetValue defectSubsetValue)
... | transportCorrectionOwner =
  ℚRing.solve-∀ (greenPairAtom family sourceSubsetValue defectSubsetValue)

correlatedResidualReconstructedFromOwners : ∀ family →
  correlatedResidualTotal family
  ≡ Sums.sumRational correlatedResidualOwners
      (ownerContribution family)
correlatedResidualReconstructedFromOwners family =
  let
    rawByOwner = trans
      (Sums.sumRationalCong
        Cube.nonemptySubsets4
        (rawLocalizationAtom family)
        (λ subset →
          Sums.sumRational correlatedResidualOwners
            (λ owner → ownedRawAtom family owner subset))
        (rawAtomReconstructedFromOwners family))
      (Fubini.sumSwap
        Cube.nonemptySubsets4 correlatedResidualOwners
        (λ subset owner → ownedRawAtom family owner subset))

    greenByOwner = trans
      (Sums.sumRationalCong
        Cube.nonemptySubsets4
        (λ sourceSubsetValue →
          Sums.sumRational Cube.nonemptySubsets4
            (λ defectSubsetValue →
              - greenPairAtom family sourceSubsetValue defectSubsetValue))
        (λ sourceSubsetValue →
          Sums.sumRational correlatedResidualOwners
            (λ owner →
              Sums.sumRational Cube.nonemptySubsets4
                (ownedGreenPairAtom family owner sourceSubsetValue)))
        (λ sourceSubsetValue → trans
          (Sums.sumRationalCong
            Cube.nonemptySubsets4
            (λ defectSubsetValue →
              - greenPairAtom family sourceSubsetValue defectSubsetValue)
            (λ defectSubsetValue →
              Sums.sumRational correlatedResidualOwners
                (λ owner → ownedGreenPairAtom family owner
                  sourceSubsetValue defectSubsetValue))
            (greenPairReconstructedFromOwners family sourceSubsetValue))
          (Fubini.sumSwap
            Cube.nonemptySubsets4 correlatedResidualOwners
            (λ defectSubsetValue owner →
              ownedGreenPairAtom family owner
                sourceSubsetValue defectSubsetValue))))
      (Fubini.sumSwap
        Cube.nonemptySubsets4 correlatedResidualOwners
        (λ sourceSubsetValue owner →
          Sums.sumRational Cube.nonemptySubsets4
            (ownedGreenPairAtom family owner sourceSubsetValue)))
  in
  trans
    (cong
      (λ selected → selected - greenContractionTotal family)
      rawByOwner)
    (trans
      (cong
        (λ selected →
          Sums.sumRational correlatedResidualOwners
            (λ owner →
              Sums.sumRational Cube.nonemptySubsets4
                (ownedRawAtom family owner))
          + selected)
        (trans
          (sym (Fubini.sumRationalNegate
            Cube.nonemptySubsets4
            (λ sourceSubsetValue →
              Sums.sumRational Cube.nonemptySubsets4
                (greenPairAtom family sourceSubsetValue))))
          greenByOwner))
      (sym
        (Fubini.sumRationalAdd
          correlatedResidualOwners
          (λ owner →
            Sums.sumRational Cube.nonemptySubsets4
              (ownedRawAtom family owner))
          (λ owner →
            Sums.sumRational Cube.nonemptySubsets4
              (λ sourceSubsetValue →
                Sums.sumRational Cube.nonemptySubsets4
                  (ownedGreenPairAtom family owner sourceSubsetValue))))))

record ExactCorrelatedCancellation
    (family : CorrelatedGreenAtomFamily) : Set where
  field
    groupedExactOwnerCancels :
      ownerContribution family exactCancellationOwner ≡ 0ℚ
open ExactCorrelatedCancellation public

survivingCorrelatedResidual : CorrelatedGreenAtomFamily → ℚ
survivingCorrelatedResidual family =
  ownerContribution family rawLocalizationOwner
  + ownerContribution family multiplierGreenOwner
  + ownerContribution family collarDisplacementOwner
  + ownerContribution family transportCorrectionOwner

exactCorrelatedCancellationRemovedBeforeMajorisation :
  ∀ {family} →
  ExactCorrelatedCancellation family →
  correlatedResidualTotal family ≡ survivingCorrelatedResidual family
exactCorrelatedCancellationRemovedBeforeMajorisation {family} cancellation =
  trans
    (correlatedResidualReconstructedFromOwners family)
    (trans
      (cong
        (λ selected →
          selected
          + ownerContribution family rawLocalizationOwner
          + ownerContribution family multiplierGreenOwner
          + ownerContribution family collarDisplacementOwner
          + ownerContribution family transportCorrectionOwner)
        (groupedExactOwnerCancels cancellation))
      (ℚRing.solve-∀
        (ownerContribution family rawLocalizationOwner)
        (ownerContribution family multiplierGreenOwner)
        (ownerContribution family collarDisplacementOwner)
        (ownerContribution family transportCorrectionOwner)))

record CorrelatedOwnerBudgets
    (family : CorrelatedGreenAtomFamily)
    (charge budget : ℚ) : Set where
  field
    rawCoefficient greenCoefficient collarCoefficient transportCoefficient : ℚ
    rawUpper : ownerContribution family rawLocalizationOwner
      ≤ rawCoefficient * charge
    greenUpper : ownerContribution family multiplierGreenOwner
      ≤ greenCoefficient * charge
    collarUpper : ownerContribution family collarDisplacementOwner
      ≤ collarCoefficient * charge
    transportUpper : ownerContribution family transportCorrectionOwner
      ≤ transportCoefficient * charge
    coefficientsFit :
      rawCoefficient + greenCoefficient
      + collarCoefficient + transportCoefficient ≤ budget
open CorrelatedOwnerBudgets public

survivingCorrelatedOwnersCloseBudget :
  ∀ {family charge budget} →
  0ℚ ≤ charge →
  CorrelatedOwnerBudgets family charge budget →
  survivingCorrelatedResidual family ≤ budget * charge
survivingCorrelatedOwnersCloseBudget {charge = charge} chargeNonnegative budgets =
  let
    firstPair = ℚP.+-mono-≤ (rawUpper budgets) (greenUpper budgets)
    secondPair = ℚP.+-mono-≤ (collarUpper budgets) (transportUpper budgets)
    allFour = ℚP.+-mono-≤ firstPair secondPair
    scaledFit =
      DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact.scaleNonnegative
        charge chargeNonnegative (coefficientsFit budgets)
  in
  subst
    (λ lower → lower ≤ _)
    (ℚRing.solve-∀
      (ownerContribution _ rawLocalizationOwner)
      (ownerContribution _ multiplierGreenOwner)
      (ownerContribution _ collarDisplacementOwner)
      (ownerContribution _ transportCorrectionOwner))
    (ℚP.≤-trans
      (subst
        (λ upper → _ ≤ upper)
        (ℚRing.solve-∀
          (rawCoefficient budgets) (greenCoefficient budgets)
          (collarCoefficient budgets) (transportCoefficient budgets) charge)
        allFour)
      scaledFit)

correlatedGreenPairOwnershipLevel : ProofLevel
correlatedGreenPairOwnershipLevel = machineChecked

correlatedCancellationBeforeMajorisationLevel : ProofLevel
correlatedCancellationBeforeMajorisationLevel = machineChecked
