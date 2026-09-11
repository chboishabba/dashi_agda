{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUrsellToSubgapClusteringUpperBidiExact where

------------------------------------------------------------------------
-- BURIED-DONOR ADAPTER: URSELL CAUCHY -> R277 SUBGAP CLUSTERING
--
-- The older T2 Ursell lane already proves exponential decay of the infinite
-- connected two-point function from its physical depth-majorant/crossing data.
-- The current R275 consumer needs only the observables selected by a
-- hypothetical positive subgap mode.  This owner therefore adds no new
-- clustering estimate: it pays only the representation/order transport from
-- that older two-observable rational carrier into the current spectrum bound.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT2UrsellCauchyExact as Ursell
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record UrsellSubgapAdapter
    {UrsellObservable Observable Energy Bound : Set}
    (ursell : Ursell.InfiniteUrsellLimit UrsellObservable ℚ)
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    : Set₁ where
  field
    -- Only the consumer-selected subgap observable is represented.  A global
    -- all-observable identification would be stronger than R277 requires.
    leftObservable :
      (energy : Energy) → Gap.SubgapMode spectrum energy → Nat → UrsellObservable
    rightObservable :
      (energy : Energy) → Gap.SubgapMode spectrum energy → Nat → UrsellObservable

    rationalBound : ℚ → Bound

    -- Order transport is representation plumbing: it says the chosen Bound
    -- presentation respects the rational inequality proved by the Ursell lane.
    rationalOrderTransport : ∀ {a b : ℚ} →
      a ≤ b →
      Gap.LessEqual spectrum (rationalBound a) (rationalBound b)

    spectrumOrderTransitive : ∀ {a b c : Bound} →
      Gap.LessEqual spectrum a b →
      Gap.LessEqual spectrum b c →
      Gap.LessEqual spectrum a c

    -- Same-object weld: the spectral connected-correlation value at the
    -- selected mode/time is exactly the absolute Ursell connected response.
    selectedCorrelationIsUrsell :
      ∀ energy (mode : Gap.SubgapMode spectrum energy) time →
      Gap.connectedCorrelation spectrum
        (Gap.modeObservable spectrum energy mode) time
      ≡ rationalBound
          (Ursell.absoluteValue ursell
            (Ursell.infiniteConnected ursell
              (leftObservable energy mode time)
              (rightObservable energy mode time)))

    -- Physical support/time identification.  This is the only decay-facing
    -- adapter field: the old Ursell tail at the selected support separation is
    -- admitted below the exact envelope consumed by the spectrum theorem.
    selectedUrsellTailBelowEnvelope :
      ∀ energy (mode : Gap.SubgapMode spectrum energy) time →
      Gap.LessEqual spectrum
        (rationalBound
          (Ursell.half *
            Ursell.halfPower
              (Ursell.separationDepth ursell
                (leftObservable energy mode time)
                (rightObservable energy mode time))))
        (Gap.clusteringEnvelope spectrum
          (Gap.modeObservable spectrum energy mode) time)

open UrsellSubgapAdapter public

ursellProducesSubgapModeClusteringUpper :
  ∀ {UrsellObservable Observable Energy Bound}
    {ursell : Ursell.InfiniteUrsellLimit UrsellObservable ℚ}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  UrsellSubgapAdapter ursell spectrum →
  Gap.SubgapModeClusteringUpper spectrum
ursellProducesSubgapModeClusteringUpper
  {ursell = ursell} {spectrum = spectrum} adapter energy mode time =
  subst
    (λ correlation →
      Gap.LessEqual spectrum
        correlation
        (Gap.clusteringEnvelope spectrum
          (Gap.modeObservable spectrum energy mode) time))
    (symmetry (selectedCorrelationIsUrsell adapter energy mode time))
    (spectrumOrderTransitive adapter
      (rationalOrderTransport adapter
        (Ursell.connectedCorrelationExponentialDecay ursell
          (leftObservable adapter energy mode time)
          (rightObservable adapter energy mode time)))
      (selectedUrsellTailBelowEnvelope adapter energy mode time))
  where
  symmetry : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  symmetry refl = refl

------------------------------------------------------------------------
-- Proof-search boundary.
------------------------------------------------------------------------

ursellCauchyTailNeedsReproof : ProofLevel
ursellCauchyTailNeedsReproof = machineChecked

ursellPhysicalTreeGraphMajorantLevel : ProofLevel
ursellPhysicalTreeGraphMajorantLevel = Ursell.physicalUrsellTreeGraphMajorantLevel

ursellToSubgapRepresentationWeldLevel : ProofLevel
ursellToSubgapRepresentationWeldLevel = conditional

ursellToSubgapCompilerLevel : ProofLevel
ursellToSubgapCompilerLevel = machineChecked
