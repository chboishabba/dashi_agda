{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySUNMatrixNativeInversePlaquetteRealTraceExact where

------------------------------------------------------------------------
-- R443 SIX POSITIVE PLANES: INVERSE ORIENTATION ON THE ACTUAL SUN LINKS.
--
-- The exact original positive-plaquette boundary, inverse path, periodic
-- step and closure proofs were *already* generic in the group carrier.
-- Reuse them to show swapped ordered plane = inverse of the native
-- SU(N) matrix positive plaquette at the same physical site.
--
-- The scalar real-trace-under-inverse law is NOT trace cyclicity alone.
-- It is a separate theorem about unitary matrices (inverse = adjoint,
-- Re Tr(U*) = Re Tr(U)); preserve that precise explicit input.
-- The quaternion rational proof is a geometric donor, not a same-object
-- full matrix SU(N) real trace proof.
--
-- Wilson (1974), Balaban (1985), Creutz lattice orientation conventions;
-- original DASHI reverse-path theorem and periodic geometry retained.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact as Inverse
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Geometry
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeRationalSU2OrderedPlaquetteC3ActionExact as Ordered
import DASHI.Physics.YangMills.YMClayNativeSixPlaneC3ActualPhysicalSourceExact as Source
import DASHI.Physics.YangMills.YMClayNativeRationalSU2SixPlaneSameSourceExact as Six

-- The original same signed plaquette path, now valued in real SU(N).
sunOrderedPlaquette :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (links : Native.SUNSideFourLinks N theory)
    (site : Hodge.Site4)
    (left right : Torus.Axis4) →
  SUN.SUNMatrixElement theory
sunOrderedPlaquette theory links site left right =
  Native.sunSignedPathHolonomy theory links site
    (Ordered.orientedOrderedPlaquetteWord left right)

sunOriginalPositivePlaquetteIsOrdered :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (links : Native.SUNSideFourLinks N theory)
    (site : Hodge.Site4) (plane : Plaquette.PositivePlane4) →
  Native.sunPositivePlaquetteHolonomy theory links
      (Torus.pair site plane)
  ≡ sunOrderedPlaquette theory links site
      (Torus.first (Plaquette.planeAxes plane))
      (Torus.second (Plaquette.planeAxes plane))
sunOriginalPositivePlaquetteIsOrdered theory links site plane =
  cong (Native.sunSignedPathHolonomy theory links site)
    (Six.nativeSixPlaneBoundaryIsOrdered plane)

sunSwappedPositivePlaneIsInverse :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (links : Native.SUNSideFourLinks N theory)
    (site : Hodge.Site4) (plane : Plaquette.PositivePlane4) →
  sunOrderedPlaquette theory links site
      (Torus.second (Plaquette.planeAxes plane))
      (Torus.first (Plaquette.planeAxes plane))
  ≡ SUN.sunInverse theory
      (Native.sunPositivePlaquetteHolonomy theory links
        (Torus.pair site plane))
sunSwappedPositivePlaneIsInverse theory links site plane =
  trans
    (cong
      (Native.sunSignedPathHolonomy theory links site)
      (sym (Source.inversePositivePlaneIsSwappedWord plane)))
    (subst
      (λ start →
        Native.sunSignedPathHolonomy theory links start
          (Inverse.reverseOpposite
            (Bond.plaquetteBoundaryDirections plane))
        ≡ SUN.sunInverse theory
            (Native.sunPositivePlaquetteHolonomy theory links
              (Torus.pair site plane)))
      (Bond.plaquetteCloses
        (Geometry.periodicPlaquetteClosure Weld.three) site plane)
      (Inverse.pathHolonomyReverseOpposite
        (Geometry.periodicStepInverseLaws Weld.three)
        (Native.sunSignedRealization theory links) site
        (Bond.plaquetteBoundaryDirections plane)))

record SUNRealTraceInverseOnNative
    {Matrix Complex Scalar : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = Scalar} theory)
    : Set₁ where
  field
    -- Algebraic SU(N) matrix theorem still required: Re Tr(U†)=Re Tr(U).
    -- It is not a duplicate assumption of Wilson/Gibbs gauge invariance.
    normalizedRealTraceInverse : ∀ U →
      Trace.matrixWilsonValue traceData (SUN.sunInverse theory U)
      ≡ Trace.matrixWilsonValue traceData U
open SUNRealTraceInverseOnNative public

sunSwappedPositivePlaneRealTrace :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = Scalar} theory)
    (inverseLaw : SUNRealTraceInverseOnNative theory traceData)
    (links : Native.SUNSideFourLinks N theory)
    (site : Hodge.Site4) (plane : Plaquette.PositivePlane4) →
  Trace.matrixWilsonValue traceData
    (sunOrderedPlaquette theory links site
      (Torus.second (Plaquette.planeAxes plane))
      (Torus.first (Plaquette.planeAxes plane)))
  ≡ Trace.matrixWilsonValue traceData
    (sunOrderedPlaquette theory links site
      (Torus.first (Plaquette.planeAxes plane))
      (Torus.second (Plaquette.planeAxes plane)))
sunSwappedPositivePlaneRealTrace theory traceData inverseLaw
    links site plane =
  trans
    (cong (Trace.matrixWilsonValue traceData)
      (sunSwappedPositivePlaneIsInverse theory links site plane))
    (trans
      (normalizedRealTraceInverse inverseLaw
        (Native.sunPositivePlaquetteHolonomy theory links
          (Torus.pair site plane)))
      (cong (Trace.matrixWilsonValue traceData)
        (sunOriginalPositivePlaquetteIsOrdered theory links site plane)))
