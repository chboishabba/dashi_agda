module DASHI.Physics.YangMills.BalabanClayExactOSPullbackRecombinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions", Communications in Mathematical
-- Physics 31 (1973), 83--112. DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", Communications in
-- Mathematical Physics 42 (1975), 281--305. DOI: 10.1007/BF01608978.
--
-- Pietro Menotti and Andrea Pelissetto,
-- "General proof of Osterwalder-Schrader positivity for the Wilson action",
-- Communications in Mathematical Physics 113 (1987), 369--373.
-- DOI: 10.1007/BF01221251.
--
-- DASHI CONTRIBUTION
--
-- This is the positivity-compatible RG route that does not require a transfer
-- matrix at every intermediate block scale.  A blocked positive-time
-- observable is pulled back exactly to the original Wilson algebra; artificial
-- labels are recombined before the OS quadratic form is evaluated.  Positivity
-- then transports by equality.  Individual labelled summands need not be
-- positive, as the finite countermodel at the end proves.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data Empty : Set where

record ExactOSPullbackData
    (OriginalObservable BlockedObservable Scalar : Set) : Set₁ where
  field
    pullback : BlockedObservable → OriginalObservable
    originalOSForm : OriginalObservable → Scalar
    blockedOSForm : BlockedObservable → Scalar
    Nonnegative : Scalar → Set

    exactPullbackIdentity : ∀ blocked →
      blockedOSForm blocked ≡ originalOSForm (pullback blocked)
    originalReflectionPositive : ∀ original →
      Nonnegative (originalOSForm original)

open ExactOSPullbackData public

exactPullbackPreservesReflectionPositivity :
  ∀ {OriginalObservable BlockedObservable Scalar}
    (dataSet : ExactOSPullbackData
      OriginalObservable BlockedObservable Scalar)
    blocked →
  Nonnegative dataSet (blockedOSForm dataSet blocked)
exactPullbackPreservesReflectionPositivity dataSet blocked =
  subst (Nonnegative dataSet)
    (sym (exactPullbackIdentity dataSet blocked))
    (originalReflectionPositive dataSet (pullback dataSet blocked))

record PositiveTimePullbackData
    (OriginalObservable BlockedObservable : Set) : Set₁ where
  field
    pullback : BlockedObservable → OriginalObservable
    OriginalPositiveTime : OriginalObservable → Set
    BlockedPositiveTime : BlockedObservable → Set
    pullbackPreservesPositiveTime : ∀ blocked →
      BlockedPositiveTime blocked →
      OriginalPositiveTime (pullback blocked)

open PositiveTimePullbackData public

blockedPositiveTimeHasOriginalPositiveTimeRepresentative :
  ∀ {OriginalObservable BlockedObservable}
    (dataSet : PositiveTimePullbackData
      OriginalObservable BlockedObservable)
    blocked →
  BlockedPositiveTime dataSet blocked →
  OriginalPositiveTime dataSet (pullback dataSet blocked)
blockedPositiveTimeHasOriginalPositiveTimeRepresentative dataSet blocked =
  pullbackPreservesPositiveTime dataSet blocked

------------------------------------------------------------------------
-- A signed label may fail positivity even though the exact recombination is
-- positive.  Thus demanding positivity label-by-label is stronger than OS
-- positivity of the physical measure and can incorrectly reject exact RG
-- decompositions.  The operation below is deliberately argument-sensitive:
-- the mixed physical pair is positive, while a pair of two negative labelled
-- pieces remains negative.
------------------------------------------------------------------------

data LabelValue : Set where
  negativeLabel positiveLabel recombinedValue : LabelValue

data LabelNonnegative : LabelValue → Set where
  positiveIsNonnegative : LabelNonnegative positiveLabel
  recombinedIsNonnegative : LabelNonnegative recombinedValue

negativeLabelIsNotNonnegative : LabelNonnegative negativeLabel → Empty
negativeLabelIsNotNonnegative ()

recombineTwoLabels : LabelValue → LabelValue → LabelValue
recombineTwoLabels negativeLabel positiveLabel = recombinedValue
recombineTwoLabels positiveLabel negativeLabel = recombinedValue
recombineTwoLabels negativeLabel negativeLabel = negativeLabel
recombineTwoLabels positiveLabel positiveLabel = positiveLabel
recombineTwoLabels recombinedValue second = recombinedValue
recombineTwoLabels first recombinedValue = recombinedValue

physicalRecombinationIsNonnegative :
  LabelNonnegative (recombineTwoLabels negativeLabel positiveLabel)
physicalRecombinationIsNonnegative = recombinedIsNonnegative

negativePairDoesNotRecombinePositively :
  LabelNonnegative (recombineTwoLabels negativeLabel negativeLabel) → Empty
negativePairDoesNotRecombinePositively = negativeLabelIsNotNonnegative

exactOSPullbackLevel : ProofLevel
exactOSPullbackLevel = machineChecked

labelRecombinationBeforePositivityLevel : ProofLevel
labelRecombinationBeforePositivityLevel = machineChecked

physicalPullbackConstructionInputsLevel : ProofLevel
physicalPullbackConstructionInputsLevel = conditional
