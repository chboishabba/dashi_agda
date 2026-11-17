module DASHI.Physics.Motors.SmithFilsingerOpenBoundaryPoyntingGaussExact where

-- Formal F10 open-boundary finite Gauss weld, no simulator.
-- Reuse the CANONICAL finite forward-difference summation owner:
-- YangMillsLatticeStressWardSliceConservationExact.differencePartialTelescopes.
--
-- The Yang-Mills proof is an arithmetic statement about ANY rational flux
-- sequence; not a gauge-theory-only or periodic-space theorem.
-- This consumer applies it to three ORIENTED open axes, never pretending
-- opposite exterior faces cancel. Exterior flux stays in the work budget.
--
-- The original KSW668 full-vector Poynting theorem is pointwise. Its
-- continuity/regularity, integration quadrature, mesh convergence and
-- real-device source-current/port equality are independent open receipts.

open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Rational.Base as ℚ
import DASHI.Physics.YangMills.YangMillsLatticeStressWardSliceConservationExact as Ward

record OpenRectangularPoyntingFaces : Set₁ where
  field
    outwardX outwardY outwardZ : Nat → ℚ.ℚ
    extentX extentY extentZ : Nat

open OpenRectangularPoyntingFaces public

-- Local finite divergence is the forward difference sum along each
-- Cartesian axis. These are oriented Poynting FACE values, not an
-- independently invented atmosphere or an acoustic waveform.
threeAxisFiniteDivergence : OpenRectangularPoyntingFaces → ℚ.ℚ
threeAxisFiniteDivergence r =
  (Ward.differencePartial (outwardX r) (extentX r)
    ℚ.+ Ward.differencePartial (outwardY r) (extentY r))
      ℚ.+ Ward.differencePartial (outwardZ r) (extentZ r)

-- Both positive and negative exterior faces survive in the algebra.
-- This is NOT a periodic box, and the right side is not assumed zero.
exteriorOrientedPoyntingFlux : OpenRectangularPoyntingFaces → ℚ.ℚ
exteriorOrientedPoyntingFlux r =
  ((outwardX r (extentX r) ℚ.- outwardX r zero)
      ℚ.+ (outwardY r (extentY r) ℚ.- outwardY r zero))
      ℚ.+ (outwardZ r (extentZ r) ℚ.- outwardZ r zero)

-- Exact finite open-boundary Gauss: volume divergence = NET signed
-- exterior face flux. No numerical integration, no modelling assumptions.
-- The ONLY proof steps reuse the already formalised Yang-Mills
-- differencePartialTelescopes theorem for the three finite axes.
finiteOpenBoundaryPoyntingGauss :
  (r : OpenRectangularPoyntingFaces) →
  threeAxisFiniteDivergence r ≡ exteriorOrientedPoyntingFlux r
finiteOpenBoundaryPoyntingGauss r
  rewrite Ward.differencePartialTelescopes
            (outwardX r) (extentX r)
        | Ward.differencePartialTelescopes
            (outwardY r) (extentY r)
        | Ward.differencePartialTelescopes
            (outwardZ r) (extentZ r)
  = refl

-- The independent physical bridge to actual Maxwell fields is explicit,
-- but the finite arithmetic consequence is now a theorem, not a premise.
record PhysicalMaxwellOpenFaceAdmission : Set₁ where
  field
    faces : OpenRectangularPoyntingFaces
    timeIntegratedLocalPoyntingDivergence : ℚ.ℚ
    originalSourceBoundaryOutgoingWork : ℚ.ℚ

    -- This is NOT derivable from an abstract vector jet: requires a
    -- genuine spatial Poynting field, oriented faces, consistent units,
    -- and a justified volume quadrature / interpolation.
    fieldDivergenceMatchesFiniteFaces :
      timeIntegratedLocalPoyntingDivergence
        ≡ threeAxisFiniteDivergence faces

    -- This is the actual selected terminal/source trace and is NOT
    -- supplied by a numerical natural-current guess or a finite box.
    physicalExteriorTraceMatchesSource :
      exteriorOrientedPoyntingFlux faces
        ≡ originalSourceBoundaryOutgoingWork

-- The physically admitted local divergence, exterior signed surface flux
-- and same-original boundary work now compose through an EXACT Gauss
-- theorem, without assuming the local and boundary integrals equal.
admittedLocalPoyntingEqualsOriginalExteriorPort :
  (a : PhysicalMaxwellOpenFaceAdmission) →
  PhysicalMaxwellOpenFaceAdmission.timeIntegratedLocalPoyntingDivergence a
    ≡ PhysicalMaxwellOpenFaceAdmission.originalSourceBoundaryOutgoingWork a
admittedLocalPoyntingEqualsOriginalExteriorPort a =
  ℚPtrans
    (PhysicalMaxwellOpenFaceAdmission.fieldDivergenceMatchesFiniteFaces a)
    (ℚPtrans
      (finiteOpenBoundaryPoyntingGauss
        (PhysicalMaxwellOpenFaceAdmission.faces a))
      (PhysicalMaxwellOpenFaceAdmission.physicalExteriorTraceMatchesSource a))
  where
    ℚPtrans : ∀ {x y z : ℚ.ℚ} → x ≡ y → y ≡ z → x ≡ z
    ℚPtrans refl second = second
