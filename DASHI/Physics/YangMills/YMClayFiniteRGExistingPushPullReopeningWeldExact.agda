module DASHI.Physics.YangMills.YMClayFiniteRGExistingPushPullReopeningWeldExact where

------------------------------------------------------------------------
-- R445 exact finite PUSHFORWARD/PULLBACK/REOPENING composition.
--
-- DO NOT redefine the original projection, conditional kernel or
-- transport: use the existing SectionedProjectionProvenanceBridgeExact
-- pullback, BalabanFiniteProbabilityPartitionDisintegrationExact compiler,
-- and BalabanFiniteRGObservableReopeningExact transport/expectations.
--
-- For the SAME finite partition, the constructed conditional kernel
-- is supported on the selected original project fibre and normalized:
--
--    T (f . project) = f,
--    E_fine [f . project] = E_coarse [f].
--
-- The second equality is a genuine derived expectation identity through
-- the existing disintegration theorem, not a stipulated functor law.
-- Fibre-constant fine observables have exact coarse reopening.
--
-- Crucial boundary: Fine states here are an enumerated finite rational
-- partition (with strictly positive coarse fibre masses). Continuous
-- SU(N) physical product-Haar Gibbs measure and its conditional
-- disintegration are NOT supplied. The SU(N) blocked cylinder functional
-- in YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact has a
-- different analytic measure carrier, requiring a same-object bridge.
--
-- No new projection theory, no physical Haar, continuum, OS positivity,
-- Hamiltonian, or Clay proof. Kernel typechecking PENDING, no --safe
-- claim about transitive legacy real/group/finite-source imports.
-- Original owners: Bałaban, existing DASHI projection and RG sources.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _*_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Projection
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteProbabilityPartitionDisintegrationExact as Partition
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen

module _
    {Fine Coarse : Set}
    {states : List Fine}
    {fineWeight : Fine → ℚ}
    (partition : Partition.FiniteCoarsePartition states fineWeight)
  where

  -- The ORIGINAL finite normalized reopening compiler.
  existingReopening : Reopen.FiniteRGReopeningStep Fine Coarse
  existingReopening = Partition.compileFiniteRGReopeningStep partition

  -- The ORIGINAL generic coarse-observable pullback, on the very same
  -- project field used to construct this finite conditional kernel.
  existingObservablePullback : (Coarse → ℚ) → Fine → ℚ
  existingObservablePullback =
    Projection.pullbackObservable (Partition.project partition)

  -- Crucial no-fake-inverse step: off-fibre terms vanish, on-fibre
  -- terms use the ACTUAL original project equality.
  originalKernelPullbackPointwise :
    (observable : Coarse → ℚ) (coarse : Coarse) (fine : Fine) →
    Partition.conditionalKernel partition coarse fine
      * existingObservablePullback observable fine
    ≡
    observable coarse
      * Partition.conditionalKernel partition coarse fine
  originalKernelPullbackPointwise observable coarse fine
    with Partition.matches partition coarse fine in selected
  ... | true =
    trans
      (cong
        (λ value →
          Partition.conditionalKernel partition coarse fine
            * observable value)
        (Partition.matchProjects partition
          (Partition.matchTrue partition coarse fine selected)))
      (ℚP.*-comm
        (Partition.conditionalKernel partition coarse fine)
        (observable coarse))
  ... | false =
    ℚRing.solve-∀
      (Partition.coarseMassReciprocal partition coarse)
      (fineWeight fine)
      (observable (Partition.project partition fine))
      (observable coarse)

  -- T (f o project) = f, with original normalized conditional kernel.
  -- This is NOT a recovery theorem for arbitrary fibre-varying data.
  originalReopeningOfPullbackIsCoarse :
    (observable : Coarse → ℚ) (coarse : Coarse) →
    Reopen.transportObservable existingReopening
      (existingObservablePullback observable) coarse
    ≡ observable coarse
  originalReopeningOfPullbackIsCoarse observable coarse =
    trans
      (Sums.sumRationalCong states
        (λ fine →
          Partition.conditionalKernel partition coarse fine
            * observable (Partition.project partition fine))
        (λ fine →
          observable coarse
            * Partition.conditionalKernel partition coarse fine)
        (originalKernelPullbackPointwise observable coarse))
      (trans
        (Sums.sumRationalScale
          (observable coarse) states
          (Partition.conditionalKernel partition coarse))
        (trans
          (cong
            (observable coarse *_)
            (Partition.conditionalKernelNormalized partition coarse))
          (ℚP.*-identityʳ (observable coarse))))

  -- More general selected fine observable: the explicit factorization
  -- witness is necessary; coarse representation is not automatic.
  originalReopeningFibreConstant :
    (fineObservable : Fine → ℚ) (coarseObservable : Coarse → ℚ) →
    (∀ fine →
      fineObservable fine
      ≡ existingObservablePullback coarseObservable fine) →
    ∀ coarse →
    Reopen.transportObservable existingReopening
      fineObservable coarse
    ≡ coarseObservable coarse
  originalReopeningFibreConstant fineObservable coarseObservable
      agrees coarse =
    trans
      (Sums.sumRationalCong states
        (λ fine →
          Partition.conditionalKernel partition coarse fine
            * fineObservable fine)
        (λ fine →
          Partition.conditionalKernel partition coarse fine
            * existingObservablePullback coarseObservable fine)
        (λ fine →
          cong
            (Partition.conditionalKernel partition coarse fine *_)
            (agrees fine)))
      (originalReopeningOfPullbackIsCoarse coarseObservable coarse)

  -- Exact measure/observable duality derived from the ORIGINAL
  -- finite RG disintegration and the just-proved pullback identity.
  -- The fine and coarse expectations are those of the SAME compiler.
  originalFinitePushforwardPullbackPairing :
    (observable : Coarse → ℚ) →
    Reopen.fineExpectation existingReopening
      (existingObservablePullback observable)
    ≡ Reopen.coarseExpectation existingReopening observable
  originalFinitePushforwardPullbackPairing observable =
    trans
      (Reopen.finiteRGObservableExpectationPreserved
        existingReopening (existingObservablePullback observable))
      (Sums.sumRationalCong
        (Partition.coarseStates partition)
        (λ coarse →
          Partition.coarseMass partition coarse
            * Reopen.transportObservable existingReopening
                (existingObservablePullback observable) coarse)
        (λ coarse →
          Partition.coarseMass partition coarse * observable coarse)
        (λ coarse →
          cong
            (Partition.coarseMass partition coarse *_)
            (originalReopeningOfPullbackIsCoarse observable coarse)))

  originalFiniteFibreConstantExpectation :
    (fineObservable : Fine → ℚ) (coarseObservable : Coarse → ℚ) →
    (∀ fine →
      fineObservable fine
        ≡ existingObservablePullback coarseObservable fine) →
    Reopen.fineExpectation existingReopening fineObservable
    ≡ Reopen.coarseExpectation existingReopening coarseObservable
  originalFiniteFibreConstantExpectation fineObservable coarseObservable
      agrees =
    trans
      (Reopen.finiteRGObservableExpectationPreserved
        existingReopening fineObservable)
      (Sums.sumRationalCong
        (Partition.coarseStates partition)
        (λ coarse →
          Partition.coarseMass partition coarse
            * Reopen.transportObservable existingReopening
                fineObservable coarse)
        (λ coarse →
          Partition.coarseMass partition coarse * coarseObservable coarse)
        (λ coarse →
          cong
            (Partition.coarseMass partition coarse *_)
            (originalReopeningFibreConstant
              fineObservable coarseObservable agrees coarse)))
