module DASHI.Physics.Closure.NSTriadKNHHAntiParallelDefectSquareRound146Exact where

------------------------------------------------------------------------
-- ROUND146 / RADIAL GAP + ANTI-PARALLEL DEFECT = LOW OUTPUT
--
-- Sources:
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--   Bahouri--Chemin--Danchin, Fourier Analysis and Nonlinear PDE,
--   DOI 10.1007/978-3-642-16830-7.
--
-- For a resonant Euclidean triad p+q=k, write
--
--   r_p = |p|, r_q = |q|, r_k = |k|.
--
-- The cosine law says
--
--   r_k^2 = r_p^2 + r_q^2 + 2 p.q.
--
-- Pure ring algebra then gives the division-free identity
--
--   (r_p-r_q)^2 + 2(r_p r_q + p.q) = r_k^2.             (1)
--
-- If P=p/r_p and Q=q/r_q, the second term is exactly
--
--   r_p r_q |P+Q|^2.
--
-- Thus (1) is the square-level complementarity between the radial multiplier
-- gap and the anti-parallel angular defect.  It is deliberately stated before
-- division/square roots so it lives on the repository's weak exact field
-- carrier and can be reused by the HH signed aggregation without importing a
-- Euclidean square-root API.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

  sq : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F
  sq {F = F} x = C3.multiply F x x

  two : ∀ {r} {F : C3.RealField r} → C3.Carrier F
  two {F = F} = C3.add F (C3.one F) (C3.one F)

record ResonantRadiusDotGeometry
    {r} (F : C3.RealField r) : Set r where
  constructor resonant-radius-dot-geometry
  field
    radiusK radiusP radiusQ pDotQ : C3.Carrier F
    cosineLaw :
      sq radiusK
      ≡ C3.add F
          (C3.add F (sq radiusP) (sq radiusQ))
          (C3.multiply F two pDotQ)

open ResonantRadiusDotGeometry public

radialGapSquared :
  ∀ {r} {F : C3.RealField r} →
  ResonantRadiusDotGeometry F → C3.Carrier F
radialGapSquared G = sq (sub (radiusP G) (radiusQ G))

scaledAntiParallelDefectSquared :
  ∀ {r} {F : C3.RealField r} →
  ResonantRadiusDotGeometry F → C3.Carrier F
scaledAntiParallelDefectSquared {F = F} G =
  C3.multiply F two
    (C3.add F
      (C3.multiply F (radiusP G) (radiusQ G))
      (pDotQ G))

radialPlusAntiParallelDefectIsOutputSquare :
  ∀ {r} {F : C3.RealField r}
    (G : ResonantRadiusDotGeometry F) →
  C3.add F
    (radialGapSquared G)
    (scaledAntiParallelDefectSquared G)
  ≡ sq (radiusK G)
radialPlusAntiParallelDefectIsOutputSquare {F = F} G =
  trans algebra (sym (cosineLaw G))
  where
  module R = Field.Solver F
  algebra :
    C3.add F
      (radialGapSquared G)
      (scaledAntiParallelDefectSquared G)
    ≡
    C3.add F
      (C3.add F (sq (radiusP G)) (sq (radiusQ G)))
      (C3.multiply F two (pDotQ G))
  algebra =
    R.solve 3
      (λ rp rq d →
        (((rp R.⊕ (R.⊝ rq)) R.⊗ (rp R.⊕ (R.⊝ rq)))
          R.⊕
          ((R.Κ two) R.⊗ ((rp R.⊗ rq) R.⊕ d)))
        R.⊜
        (((rp R.⊗ rp) R.⊕ (rq R.⊗ rq))
          R.⊕ ((R.Κ two) R.⊗ d)))
      refl (radiusP G) (radiusQ G) (pDotQ G)

-- If an external geometric layer identifies an angular square A by
--
--   r_p r_q A = 2(r_p r_q + p.q),
--
-- then the full normalized-direction identity follows without division.
record NormalizedAntiParallelSquareWitness
    {r} {F : C3.RealField r}
    (G : ResonantRadiusDotGeometry F) : Set r where
  constructor normalized-antiparallel-square-witness
  field
    angularDefectSquared : C3.Carrier F
    scaledAngularMeaning :
      C3.multiply F
        (C3.multiply F (radiusP G) (radiusQ G))
        angularDefectSquared
      ≡ scaledAntiParallelDefectSquared G

open NormalizedAntiParallelSquareWitness public

radialPlusScaledAngularIsOutputSquare :
  ∀ {r} {F : C3.RealField r}
    (G : ResonantRadiusDotGeometry F)
    (W : NormalizedAntiParallelSquareWitness G) →
  C3.add F
    (radialGapSquared G)
    (C3.multiply F
      (C3.multiply F (radiusP G) (radiusQ G))
      (angularDefectSquared W))
  ≡ sq (radiusK G)
radialPlusScaledAngularIsOutputSquare {F = F} G W
  rewrite scaledAngularMeaning W =
  radialPlusAntiParallelDefectIsOutputSquare G

round146DivisionFreeRadialAngularComplementarityClosed : Bool
round146DivisionFreeRadialAngularComplementarityClosed = true

round146SquareRootOrDivisionRequired : Bool
round146SquareRootOrDivisionRequired = false

round146HHIntraShellSignedL2AggregationClosed : Bool
round146HHIntraShellSignedL2AggregationClosed = false

round146PackageAClosed : Bool
round146PackageAClosed = false

round146DivisionFreeRadialAngularComplementarityClosedIsTrue :
  round146DivisionFreeRadialAngularComplementarityClosed ≡ true
round146DivisionFreeRadialAngularComplementarityClosedIsTrue = refl

round146PackageAClosedIsFalse : round146PackageAClosed ≡ false
round146PackageAClosedIsFalse = refl
