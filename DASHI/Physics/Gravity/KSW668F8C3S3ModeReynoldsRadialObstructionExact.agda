module DASHI.Physics.Gravity.KSW668F8C3S3ModeReynoldsRadialObstructionExact where

------------------------------------------------------------------------
-- XL: SOURCE-REUSED S3/C3 MODE-ACTION FIREWALL FOR ORIGINAL F8.
--
-- Donor: DASHI.Foundations.TernaryPermutationS3LawsExact and
-- PolynomialC3S3OrbitSamplingProjectionExact; their 27-code orbits
-- are NOT the present three physical F8 radial multipole carriers.
-- YM's separate S^3 rational SU(2) design is NOT a mode symmetry.
--
-- F8 channels ell=0,2,4 have ORIGINAL dimensions d=3,7,11.
-- They share the SAME normal_order=3 SBP2, warp-force, and SAT
-- coefficient formula, so an externally supplied common function
-- can be applied in any S3 relabeling order.
--
-- However original radial origin FV uses 2*d = 6,14,22.
-- It is not invariant under cyclic permutation of the three
-- physical mode labels, nor are original d-dependent shell masses.
-- The radial operator's exact C3 commutator is the obstruction.
-- This distinction prevents false promotion of YM invariant proofs.
--
-- All exact rational finite arithmetic below; pinned Agda not run.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Foundations.TernaryPermutationS3LawsExact as OriginalS3
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Physics.Gravity.KSW668AdS5TTFiniteVolumeFirstCellRationalExact as OriginalFV

record Triple (A : Set) : Set where
  constructor triple
  field
    first second third : A
open Triple

rotate : ∀ {A : Set} → Triple A → Triple A
rotate (triple x y z) = triple y z x

map3 : ∀ {A B : Set} → (A → B) → Triple A → Triple B
map3 f (triple x y z) = triple (f x) (f y) (f z)

-- Apply the EXISTING source-owned six S3 group constructors to the
-- three abstract mode positions; this is a relabeling action only.
act : ∀ {A : Set} → Perm.TriPermutation → Triple A → Triple A
act Perm.permIdentity v = v
act Perm.permRotate v = rotate v
act Perm.permRotate2 v = rotate (rotate v)
act Perm.permSwapLowMid (triple x y z) = triple y x z
act Perm.permSwapLowHigh (triple x y z) = triple z y x
act Perm.permSwapMidHigh (triple x y z) = triple x z y

-- One function used in ALL three channels is mode-relabel natural.
-- Instantiate f with the original mode-independent normal stage
-- applied to a MODE STATE already carrying its radial source;
-- this does not assert the native radial source is equivariant.
originalCommonNormalStageS3Naturality :
  ∀ {A B : Set} (f : A → B)
    (p : Perm.TriPermutation) (x : Triple A) →
  map3 f (act p x) ≡ act p (map3 f x)
originalCommonNormalStageS3Naturality f Perm.permIdentity x = refl
originalCommonNormalStageS3Naturality f Perm.permRotate (triple x y z) = refl
originalCommonNormalStageS3Naturality f Perm.permRotate2 (triple x y z) = refl
originalCommonNormalStageS3Naturality f Perm.permSwapLowMid (triple x y z) = refl
originalCommonNormalStageS3Naturality f Perm.permSwapLowHigh (triple x y z) = refl
originalCommonNormalStageS3Naturality f Perm.permSwapMidHigh (triple x y z) = refl

sum3 : Triple ℚ → ℚ
sum3 (triple x y z) = x + y + z

mean3 : Triple ℚ → ℚ
mean3 x = ((+ 1) / 3) * sum3 x

-- Rational Reynolds operator of the ACTUAL C3 action on three
-- mode labels; for 3 sites the C3 and S3 invariant subspace
-- coincide (all coordinates equal). This is not the 27-code
-- representative SAMPLING projector from the other domain.
reynoldsC3 : Triple ℚ → Triple ℚ
reynoldsC3 x = triple (mean3 x) (mean3 x) (mean3 x)

c3MeanInvariant :
  (x y z : ℚ) →
  mean3 (rotate (triple x y z)) ≡ mean3 (triple x y z)
c3MeanInvariant x y z = solve []

c3ReynoldsIdempotent :
  (x y z : ℚ) →
  reynoldsC3 (reynoldsC3 (triple x y z))
    ≡ reynoldsC3 (triple x y z)
c3ReynoldsIdempotent x y z = refl

-- XXXVII original radial FV at j=0: (L_d V)_0 =
-- 2d*(V_1-V_0)/h². The common h^-2 is outside this operator.
nativeRadialOrigin : Triple ℚ → Triple ℚ
nativeRadialOrigin (triple x y z) =
  triple (((+ 6) / 1) * x)
         (((+ 14) / 1) * y)
         (((+ 22) / 1) * z)

radialOriginMean : Triple ℚ → Triple ℚ
radialOriginMean (triple x y z) =
  triple (((+ 14) / 1) * x)
         (((+ 14) / 1) * y)
         (((+ 14) / 1) * z)

radialOriginDeviation : Triple ℚ → Triple ℚ
radialOriginDeviation (triple x y z) =
  triple (- (((+ 8) / 1) * x))
         0ℚ
         (((+ 8) / 1) * z)

originalRadialOriginReynoldsPlusDefect :
  (x y z : ℚ) →
  nativeRadialOrigin (triple x y z)
  ≡ triple (((+ 14) / 1) * x + - (((+ 8) / 1) * x))
           (((+ 14) / 1) * y)
           (((+ 14) / 1) * z + ((+ 8) / 1) * z)
originalRadialOriginReynoldsPlusDefect x y z = refl

-- Exact [L_origin,C3] commutator (not zero):
-- L R(x)-R L(x)=(-8y,-8z,16x).
originalRadialC3Commutator :
  (x y z : ℚ) →
  nativeRadialOrigin (rotate (triple x y z))
    ≡ triple
         (((+ 14) / 1) * y + - (((+ 8) / 1) * y))
         (((+ 22) / 1) * z + - (((+ 8) / 1) * z))
         (((+ 6) / 1) * x + ((+ 16) / 1) * x
           + - (((+ 16) / 1) * x))
originalRadialC3Commutator x y z = refl

originalRadialOriginProjectedDefect :
  (x y z : ℚ) →
  mean3 (nativeRadialOrigin (triple x y z))
    ≡ ((+ 14) / 1) * mean3 (triple x y z)
       + ((+ 8) / 3) * (z + - x)
originalRadialOriginProjectedDefect x y z = solve []

-- 3 channel radial source/normal energy *weights* are unequal
-- even on the first radial shell (h=1), so cyclic mode
-- permutation without accompanying masses is NOT an energy isometry.
originalThreeOriginMasses : Triple ℚ
originalThreeOriginMasses =
  triple ((+ 1) / 24)
         ((+ 1) / 896)
         ((+ 1) / 22528)

physicalOriginMass : Triple ℚ → ℚ
physicalOriginMass (triple x y z) =
  ((+ 1) / 24) * x * x
    + ((+ 1) / 896) * y * y
    + ((+ 1) / 22528) * z * z

physicalModeC3NotEnergySymmetry :
  physicalOriginMass (triple 1ℚ 0ℚ 0ℚ)
    ≡ (+ 1) / 24
physicalModeC3NotEnergySymmetry = solve []

physicalModeRotatedDifferent :
  physicalOriginMass (rotate (triple 1ℚ 0ℚ 0ℚ))
    ≡ (+ 1) / 22528
physicalModeRotatedDifferent = solve []
