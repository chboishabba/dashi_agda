module DASHI.Physics.YangMills.YMClayOriginalWilsonNativeOSPullbackExact where

------------------------------------------------------------------------
-- R445 -> OS: ORIGINAL NATIVE SU(N) REFLECTED FORM PULLBACK.
--
-- Earlier existing owners already prove the GENERAL mathematical rule:
-- BalabanClayExactOSPullbackRecombinationExact and
-- BalabanReflectionPositiveCoarseGrainingTransportExact.
-- Here the fine/coarse expectations are NOT independent functions:
-- BOTH are the ACTUAL selected 1024-bond Wilson-Gibbs measure and the
-- exact R445 native non-Abelian side-four -> side-two block map.
--
-- For a coarse real observable F and a chosen reflection Theta,
--
--   E_{B_*mu}[ (Theta_c F) F ]
--     = E_mu[ (Theta_f (F o B)) (F o B) ]
--
-- once the real native block intertwines the reflections on F.
-- The source original cylinder-Haar congruence proves the exact same
-- expectation, and original Wilson fine RP plus positive-halfspace
-- compatibility carries nonnegativity to the coarse positive form.
--
-- IMPORTANT: the fine Wilson RP theorem and selected physical
-- reflection/positive-time compatibility are separate inputs on the
-- literal source, not assumed from the positive density.  Reflection
-- positivity does NOT require every separate CMP122 crossing R term
-- to be positive once the complete original OS form recombines.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; _*ℝ_; _<ℝ_; _≤ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact as Push
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  FineLinks : Set
  FineLinks = Variable.SUNPeriodicLinks theory 3

  CoarseLinks : Set
  CoarseLinks = Variable.SUNPeriodicLinks theory 1

  FineObservable : Set
  FineObservable = FineLinks → ℝ

  CoarseObservable : Set
  CoarseObservable = CoarseLinks → ℝ

  originalFineGibbsMeasure :
    Physical.PhysicalFiniteYMMeasure FineLinks ℝ
  originalFineGibbsMeasure =
    Push.originalFineGibbsMeasure
      theory traceData exponential betaFine oneLink bilateral divide

  originalNativeBlock : FineLinks → CoarseLinks
  originalNativeBlock =
    Push.actualBlockedLinkMap
      theory traceData exponential betaFine oneLink bilateral divide

  actualCoarsePullback : CoarseObservable → FineObservable
  actualCoarsePullback observable links =
    observable (originalNativeBlock links)

  -- On the original REAL test algebra, reflection conjugation is
  -- represented by a selected reflection operator.  A complex-valued
  -- theorem must retain its adjoint/complex-conjugation operation.
  originalFineOSQuadratic :
    (fineReflect : FineObservable → FineObservable) →
    FineObservable → ℝ
  originalFineOSQuadratic fineReflect observable =
    Physical.normalizedExpectation originalFineGibbsMeasure
      (λ fine →
        fineReflect observable fine *ℝ observable fine)

  actualR445CoarseOSQuadratic :
    (coarseReflect : CoarseObservable → CoarseObservable) →
    CoarseObservable → ℝ
  actualR445CoarseOSQuadratic coarseReflect observable =
    Push.actualPushforwardNormalized
      theory traceData exponential betaFine oneLink bilateral divide
      (λ coarse →
        coarseReflect observable coarse *ℝ observable coarse)

  -- The *only* blocked reflection identity paid by geometry: the
  -- original native non-Abelian block commutes with the chosen actual
  -- reflection on all selected coarse physical observables.
  NativeBlockReflectsExactly :
    (fineReflect : FineObservable → FineObservable)
    (coarseReflect : CoarseObservable → CoarseObservable) →
    Set
  NativeBlockReflectsExactly fineReflect coarseReflect =
    ∀ observable fine →
      fineReflect (actualCoarsePullback observable) fine
      ≡ coarseReflect observable (originalNativeBlock fine)

  -- This is a SAME PHYSICAL MEASURE proof, not a generic fiat
  -- "coarse reflection positivity" record.
  originalR445ReflectedQuadraticIsFineWilsonQuadratic :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value)
    (fineReflect : FineObservable → FineObservable)
    (coarseReflect : CoarseObservable → CoarseObservable) →
    NativeBlockReflectsExactly fineReflect coarseReflect →
    ∀ observable →
    originalFineOSQuadratic
      fineReflect (actualCoarsePullback observable)
    ≡ actualR445CoarseOSQuadratic coarseReflect observable
  originalR445ReflectedQuadraticIsFineWilsonQuadratic
      ordered strictToWeak fineReflect coarseReflect
      compatible observable =
    cong
      (λ numerator →
        divide numerator
          (Physical.partitionFunction originalFineGibbsMeasure))
      (Finite.haarIntegralCongruent
        (Push.originalFineIntegrationLaws
          theory traceData exponential betaFine
          oneLink bilateral divide ordered strictToWeak)
        (λ fine →
          Physical.density originalFineGibbsMeasure fine
          *ℝ
          (fineReflect (actualCoarsePullback observable) fine
            *ℝ actualCoarsePullback observable fine))
        (λ fine →
          Physical.density originalFineGibbsMeasure fine
          *ℝ
          (coarseReflect observable (originalNativeBlock fine)
            *ℝ observable (originalNativeBlock fine)))
        (λ fine →
          cong
            (λ product →
              Physical.density originalFineGibbsMeasure fine
              *ℝ product)
            (cong₂ _*ℝ_ (compatible observable fine) refl)))

  -- Positivity of the WHOLE coarse OS form from the original Wilson
  -- fine form. No crossing-polymer coefficientwise PSD is assumed.
  originalR445OSReflectionPositiveFromSameFineWilson :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value)
    (fineReflect : FineObservable → FineObservable)
    (coarseReflect : CoarseObservable → CoarseObservable)
    (FinePositiveTime : FineObservable → Set)
    (CoarsePositiveTime : CoarseObservable → Set)
    (compatible : NativeBlockReflectsExactly fineReflect coarseReflect)
    (positiveTimePullback : ∀ observable →
      CoarsePositiveTime observable →
      FinePositiveTime (actualCoarsePullback observable))
    (literalWilsonFineRP : ∀ observable →
      FinePositiveTime observable →
      0ℝ ≤ℝ originalFineOSQuadratic fineReflect observable) →
    ∀ observable →
    CoarsePositiveTime observable →
    0ℝ ≤ℝ actualR445CoarseOSQuadratic coarseReflect observable
  originalR445OSReflectionPositiveFromSameFineWilson
      ordered strictToWeak fineReflect coarseReflect
      FinePositiveTime CoarsePositiveTime
      compatible positiveTimePullback literalWilsonFineRP
      observable positive =
    subst
      (λ form → 0ℝ ≤ℝ form)
      (originalR445ReflectedQuadraticIsFineWilsonQuadratic
        ordered strictToWeak fineReflect coarseReflect
        compatible observable)
      (literalWilsonFineRP
        (actualCoarsePullback observable)
        (positiveTimePullback observable positive))

-- Reflection compatibility of the original 64-block ordered native map,
-- fine Wilson OS positivity for the selected physical plane, and actual
-- positive-time support are the theorem-bearing M.04 physical inputs.
-- No positivity claim is made for isolated CMP122 crossing R fragments.
