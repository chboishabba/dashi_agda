module DASHI.Core.ThresholdKernelRenormalisation where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; pos)
open import DASHI.Core.NonlinearExplodedSparsity
open import DASHI.Core.ExplodedGraphGeometry

------------------------------------------------------------------------
-- Fine/coarse kernel comparison
------------------------------------------------------------------------

record KernelCoarseGraining
  {Xf Xc Lf Lc : Set}
  (fine : ThresholdKernel Xf Lf)
  (coarse : ThresholdKernel Xc Lc) : Set₁ where
  field
    coarseNode : Xf → Xc
    coarseState : State Xf → State Xc

open KernelCoarseGraining public

CommutationDefect :
  {Xf Xc Lf Lc : Set}
  {fine : ThresholdKernel Xf Lf}
  {coarse : ThresholdKernel Xc Lc} →
  KernelCoarseGraining fine coarse → State Xf → Xc → Set
CommutationDefect {fine = fine} {coarse = coarse} Q s x =
  ¬ (coarseState Q (applyKernel fine s) x ≡
     applyKernel coarse (coarseState Q s) x)

record CommutesExactly
  {Xf Xc Lf Lc : Set}
  {fine : ThresholdKernel Xf Lf}
  {coarse : ThresholdKernel Xc Lc}
  (Q : KernelCoarseGraining fine coarse) : Set₁ where
  field
    commutes : (s : State Xf) (x : Xc) →
      coarseState Q (applyKernel fine s) x ≡
      applyKernel coarse (coarseState Q s) x

------------------------------------------------------------------------
-- Locality preservation/destruction are explicit certificates
------------------------------------------------------------------------

record LocalityPreserving
  {Xf Xc Lf Lc : Set}
  {fine : ThresholdKernel Xf Lf}
  {coarse : ThresholdKernel Xc Lc}
  (Gf : GraphGeometry Xf)
  (Gc : GraphGeometry Xc)
  (Q : KernelCoarseGraining fine coarse) : Set₁ where
  field
    edgePreserved : {x y : Xf} →
      GraphGeometry.edge Gf x y →
      GraphGeometry.edge Gc (coarseNode Q x) (coarseNode Q y)

record LocalityDestroyed
  {Xf Xc Lf Lc : Set}
  {fine : ThresholdKernel Xf Lf}
  {coarse : ThresholdKernel Xc Lc}
  (Gf : GraphGeometry Xf)
  (Gc : GraphGeometry Xc)
  (Q : KernelCoarseGraining fine coarse) : Set₁ where
  field
    witnessLeft witnessRight : Xf
    fineEdge : GraphGeometry.edge Gf witnessLeft witnessRight
    coarseEdgeLost : ¬
      GraphGeometry.edge Gc
        (coarseNode Q witnessLeft)
        (coarseNode Q witnessRight)

------------------------------------------------------------------------
-- Preservation/collapse certificates
------------------------------------------------------------------------

record ExplodedSupportPreserved
  {Xf Xc Lf Lc : Set}
  {fine : ThresholdKernel Xf Lf}
  {coarse : ThresholdKernel Xc Lc}
  (Q : KernelCoarseGraining fine coarse)
  (s : State Xf) : Set₁ where
  field
    activeForward : (x : Xf) → ¬ (s x ≡ DASHI.Algebra.Trit.zer) →
      ¬ (coarseState Q s (coarseNode Q x) ≡ DASHI.Algebra.Trit.zer)
    neutralForward : (x : Xf) → s x ≡ DASHI.Algebra.Trit.zer →
      coarseState Q s (coarseNode Q x) ≡ DASHI.Algebra.Trit.zer

record AllPositiveCollapse
  {Xf Xc Lf Lc : Set}
  {fine : ThresholdKernel Xf Lf}
  {coarse : ThresholdKernel Xc Lc}
  (Q : KernelCoarseGraining fine coarse)
  (s : State Xf) : Set₁ where
  field
    allPositive : (x : Xc) → coarseState Q s x ≡ pos
    coarseClosed : KernelClosed coarse (coarseState Q s)

record FiniteCoarseRunCertificate
  {Xf Xc Lf Lc : Set}
  {fine : ThresholdKernel Xf Lf}
  {coarse : ThresholdKernel Xc Lc}
  (Q : KernelCoarseGraining fine coarse)
  (s : State Xf) : Set₁ where
  field
    steps : Nat
    commutationDefects : Xc → Set
    commutationDefectsExact : (x : Xc) →
      commutationDefects x ↔ CommutationDefect Q s x
    finalState : State Xc
    finalClosed : KernelClosed coarse finalState

------------------------------------------------------------------------
-- Safe theorem boundary
------------------------------------------------------------------------

localityPreservationIsNotKernelCommutation :
  {Xf Xc Lf Lc : Set}
  {fine : ThresholdKernel Xf Lf}
  {coarse : ThresholdKernel Xc Lc}
  {Gf : GraphGeometry Xf} {Gc : GraphGeometry Xc}
  {Q : KernelCoarseGraining fine coarse} →
  LocalityPreserving Gf Gc Q → LocalityPreserving Gf Gc Q
localityPreservationIsNotKernelCommutation certificate = certificate

-- No theorem derives collapse from locality destruction alone.  Particular
-- random/degree/ROI/radius runs enter through FiniteCoarseRunCertificate or
-- AllPositiveCollapse witnesses.
