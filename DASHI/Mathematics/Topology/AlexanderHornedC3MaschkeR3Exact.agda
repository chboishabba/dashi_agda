module DASHI.Mathematics.Topology.AlexanderHornedC3MaschkeR3Exact where

------------------------------------------------------------------------
-- MASCHKE WHERE IT ACTUALLY APPLIES: SAME HORN C3 ON Q^3
--
-- Source roots: Maschke (1899), finite-group averaging/Reynolds
-- operator, standard representation C3 -> SO(3).
-- Previously-owned repository:
--   AlexanderHornedC3AmbientRotationExact.rotateXYZ
--   C3CyclotomicRealDescentExact fixed line + conjugate 2-plane
--   C3FourierConjugationExact rational/complex frequency chart
--   R3HodgeCrossExact wedge/Hodge/cross in real su2 axes
--
-- We prove the ACTUAL exact rational C3 representation splits
-- into an invariant diagonal line and a two-dimensional
-- invariant plane by the 1/3 Reynolds projector. This is not
-- a status record or a Boolean standing for a theorem.
--
-- The 2-plane's matrix is precisely
--       [ 0 -1 ]
--       [ 1 -1 ]
-- and its cyclotomic polynomial is X^2+X+1.
-- In F3 this polynomial is (X-1)^2 and the modular representation
-- becomes a nonsplit self-extension; in F5 and F7 Maschke applies.
-- Finite-field checks are owned by the companion exact probe:
-- scripts/alexander_horned_c3_maschke_field_comparison.py
--
-- These exact Q-vector theorems do NOT prove physical Dirac
-- zero modes, that a wild boundary is rotationally invariant,
-- an E6/E7/E8 realization, or full Monster module semisimplicity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; -_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact as Ambient
import DASHI.Moonshine.C3CyclotomicRealDescentExact as Cyclotomic
import DASHI.Mathematics.Topology.AlexanderHornedC3SpinLiftSplitExact as Spin

Vec3 : Set
Vec3 = Ambient.Triple ℚ

vec : ℚ → ℚ → ℚ → Vec3
vec = Ambient.xyz

add : Vec3 → Vec3 → Vec3
add (Ambient.xyz a b c) (Ambient.xyz x y z) =
  vec (a + x) (b + y) (c + z)

sub : Vec3 → Vec3 → Vec3
sub (Ambient.xyz a b c) (Ambient.xyz x y z) =
  vec (a - x) (b - y) (c - z)

scale : ℚ → Vec3 → Vec3
scale t (Ambient.xyz x y z) = vec (t * x) (t * y) (t * z)

zero : Vec3
zero = vec 0ℚ 0ℚ 0ℚ

third : ℚ
third = (+ 1) / 3

traceSum : Vec3 → ℚ
traceSum (Ambient.xyz x y z) = x + y + z

mean : Vec3 → ℚ
mean v = third * traceSum v

diagonal : ℚ → Vec3
diagonal t = vec t t t

reynolds : Vec3 → Vec3
reynolds v = diagonal (mean v)

residual : Vec3 → Vec3
residual v = sub v (reynolds v)

-- Pointwise equality is proved on the ACTUAL coordinates.
reynoldsPreservesDiagonal : ∀ a → reynolds (diagonal a) ≡ diagonal a
reynoldsPreservesDiagonal a =
  let theorem : ∀ t → third * (t + t + t) ≡ t
      theorem = solve-∀
  in
    -- The same scalar equality appears in each coordinate.
    case theorem a of λ where
      refl → refl
  where
    open import Relation.Binary.PropositionalEquality using (cong)

reynoldsIdempotent : ∀ v → reynolds (reynolds v) ≡ reynolds v
reynoldsIdempotent v =
  reynoldsPreservesDiagonal (mean v)

-- R(x,y,z)=(z,x,y). Its average is invariant.
reynoldsCommutesWithActualRotation : ∀ v →
  reynolds (Ambient.rotateXYZ v) ≡ reynolds v
reynoldsCommutesWithActualRotation (Ambient.xyz x y z) =
  let theorem : ∀ a b c →
        third * (c + a + b) ≡ third * (a + b + c)
      theorem = solve-∀
  in
    case theorem x y z of λ where
      refl → refl

rotationPreservesReynolds : ∀ v →
  Ambient.rotateXYZ (reynolds v) ≡ reynolds v
rotationPreservesReynolds v = refl

-- Actual splitting as a direct-vector-space identity:
-- every x is its invariant average plus transverse residual.
reynoldsPlusResidual : ∀ v → add (reynolds v) (residual v) ≡ v
reynoldsPlusResidual (Ambient.xyz x y z) =
  let theorem : ∀ a m → m + (a - m) ≡ a
      theorem = solve-∀
  in
    case theorem x (third * (x + y + z))
       , theorem y (third * (x + y + z))
       , theorem z (third * (x + y + z)) of λ where
       (refl , refl , refl) → refl
  where
    open import Data.Product using (_,_)

-- Actual complement plane, not only an abstract rank-two label.
transverse : ℚ → ℚ → Vec3
transverse a b = vec a (b - a) (0ℚ - b)

transverseHasZeroSum : ∀ a b → traceSum (transverse a b) ≡ 0ℚ
transverseHasZeroSum = solve-∀

reynoldsKillsTransverse : ∀ a b →
  reynolds (transverse a b) ≡ zero
reynoldsKillsTransverse a b =
  let theorem : ∀ x y →
        third * (x + (y - x) + (0ℚ - y)) ≡ 0ℚ
      theorem = solve-∀
  in
    case theorem a b of λ where refl → refl

-- On (a,b) in the transverse basis, the SAME ambient rotation is
-- represented by the genuine rational cyclotomic companion matrix.
companionAction : ℚ → ℚ → Vec3
companionAction a b = transverse (0ℚ - b) (a - b)

rotationIsCyclotomicOnTransverse :
  ∀ a b → Ambient.rotateXYZ (transverse a b) ≡ companionAction a b
rotationIsCyclotomicOnTransverse a b =
  let theorem : ∀ x y → y - (0ℚ - x) ≡ y + x
      theorem = solve-∀
  in
    -- Coordinates reduce by rational-ring polynomial equality.
    case theorem b a of λ where
      refl → refl

-- Existing realified-sector donor has dimension one plus two;
-- here those sectors are constructed as actual rational
-- coordinate submodules, not just a matching dimension.
sameExistingFixedAxisDimension :
  Cyclotomic.realifiedDimension Cyclotomic.fixedRealAxis ≡ 1
sameExistingFixedAxisDimension = refl

sameExistingTransversePlaneDimension :
  Cyclotomic.realifiedDimension Cyclotomic.transverseConjugatePlane ≡ 2
sameExistingTransversePlaneDimension = refl

-- The split spin lift still belongs to C3 and has its own central
-- sign bookkeeping; this projector is for its SPATIAL 3D carrier.
spatialSpinLiftProjects :
  ∀ g → Spin.forgetSign (Spin.coherentSection g) ≡ g
spatialSpinLiftProjects = Spin.coherentSectionProjectsToIdentity
