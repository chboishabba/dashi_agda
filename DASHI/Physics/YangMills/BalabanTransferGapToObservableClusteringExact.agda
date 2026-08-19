module DASHI.Physics.YangMills.BalabanTransferGapToObservableClusteringExact where

------------------------------------------------------------------------
-- ROUND66: TRANSFER GAP -> OBSERVABLE CLUSTERING
--
-- PRIMARY SOURCES
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- James Glimm and Arthur Jaffe,
-- "Quantum Physics: A Functional Integral Point of View", 2nd ed.
-- DOI: 10.1007/978-1-4612-4728-9.
--
-- DASHI CONTRIBUTION
--
-- The previous eleven-leaf cutset counted
--
--   common transfer gap -> finite-cutoff observable clustering
--
-- as a separate physical analytic leaf.  Once the SAME gauge-invariant
-- observable is represented by its centered transfer-Hilbert-space vector and
-- the orthogonal-to-vacuum semigroup already carries the common exponential
-- norm decay, the correlation estimate is only Cauchy--Schwarz plus monotonicity.
--
-- Consequently the remaining Yang--Mills work is the same-object transfer/OS
-- identification and the common spectral floor, not another independent decay
-- inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record TransferGapObservableSemigroup
    (Observable Vector Time Scalar Bound : Set) : Set₁ where
  field
    centeredVector : Observable → Vector
    semigroup : Time → Vector → Vector

    vectorNorm : Vector → Bound
    connectedMagnitude : Observable → Observable → Time → Bound
    gapDecay : Time → Bound

    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    lessEqualTransitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    multiplyLeftMonotone : ∀ factor {left right} →
      LessEqual left right →
      LessEqual (multiply factor left) (multiply factor right)

    -- Same-object transfer representation + Hilbert Cauchy--Schwarz.
    correlationCauchySchwarz : ∀ A B t →
      LessEqual
        (connectedMagnitude A B t)
        (multiply (vectorNorm (centeredVector A))
          (vectorNorm (semigroup t (centeredVector B))))

    -- Spectral theorem consequence of a common transfer gap on the
    -- vacuum-orthogonal sector.
    vacuumOrthogonalSemigroupDecay : ∀ B t →
      LessEqual
        (vectorNorm (semigroup t (centeredVector B)))
        (multiply (gapDecay t) (vectorNorm (centeredVector B)))

open TransferGapObservableSemigroup public

observableClusteringFromTransferGap :
  ∀ {Observable Vector Time Scalar Bound}
    (dataSet : TransferGapObservableSemigroup
      Observable Vector Time Scalar Bound) →
    ∀ A B t →
  LessEqual dataSet
    (connectedMagnitude dataSet A B t)
    (multiply dataSet
      (vectorNorm dataSet (centeredVector dataSet A))
      (multiply dataSet
        (gapDecay dataSet t)
        (vectorNorm dataSet (centeredVector dataSet B))))
observableClusteringFromTransferGap dataSet A B t =
  lessEqualTransitive dataSet
    (correlationCauchySchwarz dataSet A B t)
    (multiplyLeftMonotone dataSet
      (vectorNorm dataSet (centeredVector dataSet A))
      (vacuumOrthogonalSemigroupDecay dataSet B t))

record CutoffUniformTransferGapObservableFamily
    (Cutoff Observable Vector Time Scalar Bound : Set) : Set₁ where
  field
    dataAt : Cutoff →
      TransferGapObservableSemigroup Observable Vector Time Scalar Bound
    commonGapDecay : Time → Bound
    gapDecayIsCommon : ∀ cutoff time →
      gapDecay (dataAt cutoff) time ≡ commonGapDecay time

open CutoffUniformTransferGapObservableFamily public

transferGapToObservableClusteringCompilerLevel : ProofLevel
transferGapToObservableClusteringCompilerLevel = machineChecked

transferGapSemigroupDecayStandardLevel : ProofLevel
transferGapSemigroupDecayStandardLevel = standardImported

literalObservableTransferRepresentationLevel : ProofLevel
literalObservableTransferRepresentationLevel = conditional
