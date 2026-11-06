{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySUNMatrixNativeSixPlaneC3FromInverseTraceExact where

------------------------------------------------------------------------
-- PHYSICAL R443: EXACT SIX ORIGINAL SUN PLAQUETTES, ALL REAL MATRIX LINKS.
--
-- The original quaternion proof identified the two reversed planes. Here
-- we reuse its *group-independent* signed-word geometry and the original
-- SUN signed holonomy and original positive-plane enumeration.
-- A single real matrix trace-inversion authority is the only additional
-- scalar source input. The six-plane C3 permutation is proved with the
-- existing real additive laws; no postulated whole action/C3 equality.
--
-- This is still a finite side-four result. It is not an actual concrete
-- complex matrix constructor, compact SU(N) Haar or continuum mass gap.
-- Wilson (1974), Balaban (1985); original DASHI proof owners preserved.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; +-assoc; +-comm)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as Gibbs
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeInversePlaquetteRealTraceExact as Inverse
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeRationalSU2OrderedPlaquetteC3ActionExact as Ordered
import DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceExact as C3

-- Reassociate and commute ONLY the six real scalar terms. No real ring
-- solver is invoked: existing real addition is commutative and associative.
rotateThreeReal :
  ∀ a b c rest →
  a +ℝ (b +ℝ (c +ℝ rest))
  ≡ b +ℝ (c +ℝ (a +ℝ rest))
rotateThreeReal a b c rest =
  trans
    (sym (+-assoc a b (c +ℝ rest)))
    (trans
      (cong (λ p → p +ℝ (c +ℝ rest)) (+-comm a b))
      (trans
        (+-assoc b a (c +ℝ rest))
        (cong (b +ℝ_)
          (trans
            (sym (+-assoc a c rest))
            (trans
              (cong (λ p → p +ℝ rest) (+-comm a c))
              (+-assoc c a rest))))))

sixRealC3Reindex :
  ∀ a b c d e f →
  b +ℝ (c +ℝ (a +ℝ (f +ℝ (d +ℝ (e +ℝ 0ℝ)))))
  ≡
  a +ℝ (b +ℝ (c +ℝ (d +ℝ (e +ℝ (f +ℝ 0ℝ)))))
sixRealC3Reindex a b c d e f =
  trans
    (rotateThreeReal b c a (f +ℝ (d +ℝ (e +ℝ 0ℝ))))
    (trans
      (rotateThreeReal c a b (f +ℝ (d +ℝ (e +ℝ 0ℝ))))
      (cong (λ tail → a +ℝ (b +ℝ (c +ℝ tail)))
        (rotateThreeReal f d e 0ℝ)))

sunOrderedDeficit :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (links : Native.SUNSideFourLinks N theory)
    (site : Hodge.Site4)
    (left right : Torus.Axis4) → ℝ
sunOrderedDeficit theory traceData links site left right =
  1ℝ -ℝ Trace.matrixWilsonValue traceData
    (Inverse.sunOrderedPlaquette theory links site left right)

sunOrderedDeficitC3 :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (links : Native.SUNSideFourLinks N theory)
    site left right →
  sunOrderedDeficit theory traceData
    (Weld.nativeForwardC3Bonds links) site left right
  ≡ sunOrderedDeficit theory traceData links
      (C3.spatialC3Site site)
      (C3.spatialC3Axis left) (C3.spatialC3Axis right)
sunOrderedDeficitC3 theory traceData links site left right =
  cong (1ℝ -ℝ_)
    (trans
      (Native.sunSignedC3Wilson theory
        (Trace.matrixWilsonValue traceData) links site
        (Ordered.orientedOrderedPlaquetteWord left right))
      (cong
        (λ word → Trace.matrixWilsonValue traceData
          (Native.sunSignedPathHolonomy theory links
            (C3.spatialC3Site site) word))
        (Ordered.c3PlaquetteWord left right)))

sunOrderedDeficitSwapped :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (inverseLaw : Inverse.SUNRealTraceInverseOnNative theory traceData)
    (links : Native.SUNSideFourLinks N theory)
    site plane →
  sunOrderedDeficit theory traceData links site
    (Torus.second (Plaquette.planeAxes plane))
    (Torus.first (Plaquette.planeAxes plane))
  ≡ sunOrderedDeficit theory traceData links site
    (Torus.first (Plaquette.planeAxes plane))
    (Torus.second (Plaquette.planeAxes plane))
sunOrderedDeficitSwapped theory traceData inverseLaw links site plane =
  cong (1ℝ -ℝ_)
    (Inverse.sunSwappedPositivePlaneRealTrace
      theory traceData inverseLaw links site plane)

sunSixOrderedDeficitAt :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (links : Native.SUNSideFourLinks N theory)
    (site : Hodge.Site4) → ℝ
sunSixOrderedDeficitAt theory traceData links site =
  sunOrderedDeficit theory traceData links site Hodge.axis0 Hodge.axis1 +ℝ
   (sunOrderedDeficit theory traceData links site Hodge.axis0 Hodge.axis2 +ℝ
   (sunOrderedDeficit theory traceData links site Hodge.axis0 Hodge.axis3 +ℝ
   (sunOrderedDeficit theory traceData links site Hodge.axis1 Hodge.axis2 +ℝ
   (sunOrderedDeficit theory traceData links site Hodge.axis1 Hodge.axis3 +ℝ
   (sunOrderedDeficit theory traceData links site Hodge.axis2 Hodge.axis3 +ℝ 0ℝ)))))

nativeSixSourceIsOrdered :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (links : Native.SUNSideFourLinks N theory)
    (site : Hodge.Site4) →
  Gibbs.nativeSUNSixWilsonDeficitAt theory traceData links site
  ≡ sunSixOrderedDeficitAt theory traceData links site
nativeSixSourceIsOrdered theory traceData links site =
  Sums.realSumCong (Plaquette.ownedPeriodicPlaquettes site)
    (λ (Torus.pair base plane) →
      cong (1ℝ -ℝ_)
        (cong (Trace.matrixWilsonValue traceData)
          (Inverse.sunOriginalPositivePlaquetteIsOrdered
            theory links base plane)))

-- There are exactly TWO reversed plane terms after time-fixed spatial C3:
-- (2,1) and (3,1). Their source-derived reversal uses just the genuine
-- SU(N) inverse-trace property, never an independent full six-plane axiom.
nativeSUNSixAtC3FromInverseRealTrace :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (inverseLaw : Inverse.SUNRealTraceInverseOnNative theory traceData)
    (links : Native.SUNSideFourLinks N theory)
    (site : Hodge.Site4) →
  Gibbs.nativeSUNSixWilsonDeficitAt theory traceData
    (Weld.nativeForwardC3Bonds links) site
  ≡ Gibbs.nativeSUNSixWilsonDeficitAt theory traceData
      links (C3.spatialC3Site site)
nativeSUNSixAtC3FromInverseRealTrace
    theory traceData inverseLaw links site
  rewrite nativeSixSourceIsOrdered theory traceData
            (Weld.nativeForwardC3Bonds links) site
        | nativeSixSourceIsOrdered theory traceData
            links (C3.spatialC3Site site)
        | sunOrderedDeficitC3 theory traceData links site
            Hodge.axis0 Hodge.axis1
        | sunOrderedDeficitC3 theory traceData links site
            Hodge.axis0 Hodge.axis2
        | sunOrderedDeficitC3 theory traceData links site
            Hodge.axis0 Hodge.axis3
        | sunOrderedDeficitC3 theory traceData links site
            Hodge.axis1 Hodge.axis2
        | sunOrderedDeficitC3 theory traceData links site
            Hodge.axis1 Hodge.axis3
        | sunOrderedDeficitC3 theory traceData links site
            Hodge.axis2 Hodge.axis3
        | sunOrderedDeficitSwapped theory traceData inverseLaw
            links (C3.spatialC3Site site)
            (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)))
        | sunOrderedDeficitSwapped theory traceData inverseLaw
            links (C3.spatialC3Site site)
            (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ
              (Torus.sucᵢ Torus.zeroᵢ))))
  = sixRealC3Reindex
      (sunOrderedDeficit theory traceData links
        (C3.spatialC3Site site) Hodge.axis0 Hodge.axis1)
      (sunOrderedDeficit theory traceData links
        (C3.spatialC3Site site) Hodge.axis0 Hodge.axis2)
      (sunOrderedDeficit theory traceData links
        (C3.spatialC3Site site) Hodge.axis0 Hodge.axis3)
      (sunOrderedDeficit theory traceData links
        (C3.spatialC3Site site) Hodge.axis1 Hodge.axis2)
      (sunOrderedDeficit theory traceData links
        (C3.spatialC3Site site) Hodge.axis1 Hodge.axis3)
      (sunOrderedDeficit theory traceData links
        (C3.spatialC3Site site) Hodge.axis2 Hodge.axis3)
