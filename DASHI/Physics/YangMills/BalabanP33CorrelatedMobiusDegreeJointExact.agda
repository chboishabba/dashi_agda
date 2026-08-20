module DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact where

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
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- The selected correlated G2 residual already removes its exact-cancellation
-- owner fibre before majorisation.  The next loss of information came from
-- intervalising all 15 raw Möbius atoms and all 15x15 Green atoms separately.
--
-- This module proves an exact degree decomposition BEFORE intervalisation.
-- The nonempty Boolean four-cube splits as 4+6+4+1 by degree.  Hence
--
--   raw = R1 + R2 + R3 + R4
--
-- and the Green contraction is a 4x4 block sum
--
--   green = sum_(d,e=1..4) G_de.
--
-- Consequently the physical correlated residual may be enclosed as four raw
-- blocks against sixteen JOINT Green blocks (or coarser combinations), retaining
-- cancellations inside each block.  No target coefficient and no numerical
-- interval is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership

infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ right = right
(x ∷ xs) ++ right = x ∷ (xs ++ right)

sumAppend :
  ∀ {A : Set} (left right : List A) (value : A → ℚ) →
  Sums.sumRational (left ++ right) value
  ≡ Sums.sumRational left value + Sums.sumRational right value
sumAppend [] right value = refl
sumAppend (x ∷ xs) right value
  rewrite sumAppend xs right value = refl

sumFourBlocks :
  ∀ {A : Set}
    (one two three four : List A) (value : A → ℚ) →
  Sums.sumRational (one ++ two ++ three ++ four) value
  ≡ Sums.sumRational one value
    + Sums.sumRational two value
    + Sums.sumRational three value
    + Sums.sumRational four value
sumFourBlocks one two three four value =
  trans
    (sumAppend one (two ++ three ++ four) value)
    (trans
      (cong (Sums.sumRational one value +_)
        (sumAppend two (three ++ four) value))
      (trans
        (cong
          (λ tail →
            Sums.sumRational one value
            + (Sums.sumRational two value + tail))
          (sumAppend three four value))
        (ℚRing.solve-∀
          (Sums.sumRational one value)
          (Sums.sumRational two value)
          (Sums.sumRational three value)
          (Sums.sumRational four value))))

degreeOrderedSubsets4 : List Cube.Subset4
degreeOrderedSubsets4 =
  Cube.singletonSubsets4
  ++ Cube.pairSubsets4
  ++ Cube.tripleSubsets4
  ++ Cube.quarticSubsets4

degreeOrderIsCanonicalNonempty :
  degreeOrderedSubsets4 ≡ Cube.nonemptySubsets4
degreeOrderIsCanonicalNonempty = refl

sumNonemptyByDegree :
  (value : Cube.Subset4 → ℚ) →
  Sums.sumRational Cube.nonemptySubsets4 value
  ≡ Sums.sumRational Cube.singletonSubsets4 value
    + Sums.sumRational Cube.pairSubsets4 value
    + Sums.sumRational Cube.tripleSubsets4 value
    + Sums.sumRational Cube.quarticSubsets4 value
sumNonemptyByDegree value =
  trans
    (cong (λ subsets → Sums.sumRational subsets value)
      (sym degreeOrderIsCanonicalNonempty))
    (sumFourBlocks
      Cube.singletonSubsets4 Cube.pairSubsets4
      Cube.tripleSubsets4 Cube.quarticSubsets4 value)

data MobiusDegree : Set where
  degree1 degree2 degree3 degree4 : MobiusDegree

degreeSubsets : MobiusDegree → List Cube.Subset4
degreeSubsets degree1 = Cube.singletonSubsets4
degreeSubsets degree2 = Cube.pairSubsets4
degreeSubsets degree3 = Cube.tripleSubsets4
degreeSubsets degree4 = Cube.quarticSubsets4

allDegrees : List MobiusDegree
allDegrees = degree1 ∷ degree2 ∷ degree3 ∷ degree4 ∷ []

rawDegreeBlock :
  Ownership.CorrelatedResidualFamily → MobiusDegree → ℚ
rawDegreeBlock family degree =
  Sums.sumRational (degreeSubsets degree)
    (Ownership.rawLocalizationAtom family)

greenDegreeBlock :
  Ownership.CorrelatedResidualFamily → MobiusDegree → MobiusDegree → ℚ
greenDegreeBlock family leftDegree rightDegree =
  Sums.sumRational (degreeSubsets leftDegree)
    (λ left →
      Sums.sumRational (degreeSubsets rightDegree)
        (Ownership.multiplierGreenAtom family left))

rawDegreeTotal : Ownership.CorrelatedResidualFamily → ℚ
rawDegreeTotal family =
  Sums.sumRational allDegrees (rawDegreeBlock family)

greenDegreeRow :
  Ownership.CorrelatedResidualFamily → MobiusDegree → ℚ
greenDegreeRow family leftDegree =
  Sums.sumRational allDegrees (greenDegreeBlock family leftDegree)

greenDegreeTotal : Ownership.CorrelatedResidualFamily → ℚ
greenDegreeTotal family =
  Sums.sumRational allDegrees (greenDegreeRow family)

rawTotalIsDegreeTotal : ∀ family →
  Ownership.rawLocalizationTotal family ≡ rawDegreeTotal family
rawTotalIsDegreeTotal family =
  trans
    (sumNonemptyByDegree (Ownership.rawLocalizationAtom family))
    refl

-- First group the right index of one Green row by Möbius degree.
greenAtLeftByRightDegree : ∀ family left →
  Sums.sumRational Cube.nonemptySubsets4
    (Ownership.multiplierGreenAtom family left)
  ≡ Sums.sumRational allDegrees
      (λ rightDegree →
        Sums.sumRational (degreeSubsets rightDegree)
          (Ownership.multiplierGreenAtom family left))
greenAtLeftByRightDegree family left =
  trans
    (sumNonemptyByDegree (Ownership.multiplierGreenAtom family left))
    refl

-- Grouping the left index needs finite-sum congruence followed by the same
-- 4+6+4+1 decomposition.  No 225-term expansion is required.
greenTotalIsDegreeTotal : ∀ family →
  Ownership.greenPairTotal family ≡ greenDegreeTotal family
greenTotalIsDegreeTotal family =
  let
    rightGrouped :
      Sums.sumRational Cube.nonemptySubsets4
        (λ left →
          Sums.sumRational Cube.nonemptySubsets4
            (Ownership.multiplierGreenAtom family left))
      ≡ Sums.sumRational Cube.nonemptySubsets4
          (λ left →
            Sums.sumRational allDegrees
              (λ rightDegree →
                Sums.sumRational (degreeSubsets rightDegree)
                  (Ownership.multiplierGreenAtom family left)))
    rightGrouped =
      Sums.sumRationalCong Cube.nonemptySubsets4
        (λ left →
          Sums.sumRational Cube.nonemptySubsets4
            (Ownership.multiplierGreenAtom family left))
        (λ left →
          Sums.sumRational allDegrees
            (λ rightDegree →
              Sums.sumRational (degreeSubsets rightDegree)
                (Ownership.multiplierGreenAtom family left)))
        (greenAtLeftByRightDegree family)

    leftGrouped =
      sumNonemptyByDegree
        (λ left →
          Sums.sumRational allDegrees
            (λ rightDegree →
              Sums.sumRational (degreeSubsets rightDegree)
                (Ownership.multiplierGreenAtom family left)))
  in
  trans rightGrouped
    (trans leftGrouped
      (ℚRing.solve-∀
        (greenDegreeBlock family degree1 degree1)
        (greenDegreeBlock family degree1 degree2)
        (greenDegreeBlock family degree1 degree3)
        (greenDegreeBlock family degree1 degree4)
        (greenDegreeBlock family degree2 degree1)
        (greenDegreeBlock family degree2 degree2)
        (greenDegreeBlock family degree2 degree3)
        (greenDegreeBlock family degree2 degree4)
        (greenDegreeBlock family degree3 degree1)
        (greenDegreeBlock family degree3 degree2)
        (greenDegreeBlock family degree3 degree3)
        (greenDegreeBlock family degree3 degree4)
        (greenDegreeBlock family degree4 degree1)
        (greenDegreeBlock family degree4 degree2)
        (greenDegreeBlock family degree4 degree3)
        (greenDegreeBlock family degree4 degree4)))

correlatedResidualIsJointDegreeExpression : ∀ family →
  Ownership.correlatedResidualTotal family
  ≡ rawDegreeTotal family - greenDegreeTotal family
correlatedResidualIsJointDegreeExpression family =
  cong₂ _-_ (rawTotalIsDegreeTotal family) (greenTotalIsDegreeTotal family)

------------------------------------------------------------------------
-- Owner x degree blocks: combine with the existing exact owner cancellation
-- before any interval majorisation.
------------------------------------------------------------------------

selectedRawDegreeBlock :
  Ownership.CorrelatedResidualFamily →
  Ownership.CorrelatedResidualOwner → MobiusDegree → ℚ
selectedRawDegreeBlock family owner degree =
  Sums.sumRational (degreeSubsets degree)
    (Ownership.selectedRawAtom family owner)

selectedGreenDegreeBlock :
  Ownership.CorrelatedResidualFamily →
  Ownership.CorrelatedResidualOwner →
  MobiusDegree → MobiusDegree → ℚ
selectedGreenDegreeBlock family owner leftDegree rightDegree =
  Sums.sumRational (degreeSubsets leftDegree)
    (λ left →
      Sums.sumRational (degreeSubsets rightDegree)
        (Ownership.selectedGreenAtom family owner left))

ownerDegreeContribution :
  Ownership.CorrelatedResidualFamily →
  Ownership.CorrelatedResidualOwner → MobiusDegree → ℚ
ownerDegreeContribution family owner leftDegree =
  selectedRawDegreeBlock family owner leftDegree
  - Sums.sumRational allDegrees
      (selectedGreenDegreeBlock family owner leftDegree)

ownerContributionIsDegreeSum : ∀ family owner →
  Ownership.ownerContribution family owner
  ≡ Sums.sumRational allDegrees
      (ownerDegreeContribution family owner)
ownerContributionIsDegreeSum family owner =
  let
    rawGrouped = sumNonemptyByDegree
      (Ownership.selectedRawAtom family owner)
    rightGrouped : ∀ left →
      Sums.sumRational Cube.nonemptySubsets4
        (Ownership.selectedGreenAtom family owner left)
      ≡ Sums.sumRational allDegrees
          (λ rightDegree →
            Sums.sumRational (degreeSubsets rightDegree)
              (Ownership.selectedGreenAtom family owner left))
    rightGrouped left =
      trans
        (sumNonemptyByDegree (Ownership.selectedGreenAtom family owner left))
        refl
    greenPointwise =
      Sums.sumRationalCong Cube.nonemptySubsets4
        (λ left →
          Sums.sumRational Cube.nonemptySubsets4
            (Ownership.selectedGreenAtom family owner left))
        (λ left →
          Sums.sumRational allDegrees
            (λ rightDegree →
              Sums.sumRational (degreeSubsets rightDegree)
                (Ownership.selectedGreenAtom family owner left)))
        rightGrouped
    greenGrouped = trans greenPointwise
      (sumNonemptyByDegree
        (λ left →
          Sums.sumRational allDegrees
            (λ rightDegree →
              Sums.sumRational (degreeSubsets rightDegree)
                (Ownership.selectedGreenAtom family owner left))))
  in
  trans
    (cong₂ _-_ rawGrouped greenGrouped)
    (ℚRing.solve-∀
      (selectedRawDegreeBlock family owner degree1)
      (selectedRawDegreeBlock family owner degree2)
      (selectedRawDegreeBlock family owner degree3)
      (selectedRawDegreeBlock family owner degree4)
      (selectedGreenDegreeBlock family owner degree1 degree1)
      (selectedGreenDegreeBlock family owner degree1 degree2)
      (selectedGreenDegreeBlock family owner degree1 degree3)
      (selectedGreenDegreeBlock family owner degree1 degree4)
      (selectedGreenDegreeBlock family owner degree2 degree1)
      (selectedGreenDegreeBlock family owner degree2 degree2)
      (selectedGreenDegreeBlock family owner degree2 degree3)
      (selectedGreenDegreeBlock family owner degree2 degree4)
      (selectedGreenDegreeBlock family owner degree3 degree1)
      (selectedGreenDegreeBlock family owner degree3 degree2)
      (selectedGreenDegreeBlock family owner degree3 degree3)
      (selectedGreenDegreeBlock family owner degree3 degree4)
      (selectedGreenDegreeBlock family owner degree4 degree1)
      (selectedGreenDegreeBlock family owner degree4 degree2)
      (selectedGreenDegreeBlock family owner degree4 degree3)
      (selectedGreenDegreeBlock family owner degree4 degree4))

mobiusDegreeRawGreenDecompositionLevel : ProofLevel
mobiusDegreeRawGreenDecompositionLevel = machineChecked

mobiusOwnerDegreeDelayedMajorisationLevel : ProofLevel
mobiusOwnerDegreeDelayedMajorisationLevel = machineChecked

-- Remaining physical/numerical producer: enclose the JOINT owner-degree blocks
-- on the selected region (preferably by affine/Taylor forms sharing the same
-- background variables), then compare their summed endpoint to 55/18874368 Q_*.
selectedRegionJointDegreeIntervalProducerLevel : ProofLevel
selectedRegionJointDegreeIntervalProducerLevel = conditional
