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
-- inequality.  This module proves that implication at the exact abstract level
-- needed by the physical carrier.
------------------------------------------------------------------------

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

    -- This is the spectral theorem consequence of the common transfer gap on
    -- the vacuum-orthogonal sector: ||e^{-tH} psi|| <= e^{-m t} ||psi||.
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

    -- Same physical decay carrier at every cutoff.  This keeps cutoff
    -- uniformity out of the pointwise Cauchy--Schwarz proof.
    commonGapDecay : Time → Bound
    gapDecayIsCommon : ∀ cutoff time →
      gapDecay (dataAt cutoff) time ≡ commonGapDecay time
  where
  open import Agda.Builtin.Equality using (_≡_)

-- The pointwise theorem already applies uniformly once gapDecay is identified
-- with one cutoff-independent physical decay law.  No new lattice estimate is
-- introduced by passing from the spectral floor to observable correlations.
transferGapToObservableClusteringCompilerLevel : ProofLevel
transferGapToObservableClusteringCompilerLevel = machineChecked

transferGapSemigroupDecayStandardLevel : ProofLevel
transferGapSemigroupDecayStandardLevel = standardImported

-- Physical seam: identify centered local gauge-invariant observables with the
-- SAME transfer-Hilbert-space vectors and the Round66 common mass floor.
literalObservableTransferRepresentationLevel : ProofLevel
literalObservableTransferRepresentationLevel = conditional
