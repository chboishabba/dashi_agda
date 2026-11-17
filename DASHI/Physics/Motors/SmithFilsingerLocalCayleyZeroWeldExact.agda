module DASHI.Physics.Motors.SmithFilsingerLocalCayleyZeroWeldExact where

-- F13: EXACT coefficient-level two-coordinate Cayley update.
-- Reuse existing LocalPrimitive and dynamic Reach proof owners.
-- For A=[[0,a],[b,0]], the midpoint update is
-- (I-h A/2)^-1 (I+h A/2) =
-- q [[1+h²ab/4, h a], [h b, 1+h²ab/4]]
-- with q*(1-h²ab/4)=1.
--
-- No arbitrary Green response or source work is inferred here.
-- Physical Maxwell light cone and actual material measurements OPEN.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
import DASHI.Physics.Motors.SmithFilsingerLocalCausalADEFrameExact as Frame
import DASHI.Physics.Motors.SmithFilsingerIndexedFaceIncidenceExact as Indexed
open import Agda.Builtin.Bool using (false)
import DASHI.Physics.Motors.SmithFilsingerLocalCausalADEReachExact as Reach

-- The SOURCE-OWNED inverse denominator is explicitly certified.
-- quarterIsQuarter ties this coefficient to h²ab/4; it is NOT an
-- unspecified independently chosen matrix or an arbitrary linear gate.
record CertifiedCayley : Set where
  field
    step firstCoupling secondCoupling inverseDenominator quarter : ℚ
    inverseLaw :
      ((1ℚ - (quarter * (step * step) *
                      (firstCoupling * secondCoupling)))
        * inverseDenominator) ≡ 1ℚ
    quarterIsQuarter :
      (quarter + quarter) + (quarter + quarter) ≡ 1ℚ

open CertifiedCayley

sameCayleyFirst : CertifiedCayley → ℚ → ℚ → ℚ
sameCayleyFirst c x y =
  inverseDenominator c *
    (((1ℚ + quarter c * (step c * step c) *
                   (firstCoupling c * secondCoupling c)) * x)
       + ((step c * firstCoupling c) * y))

sameCayleySecond : CertifiedCayley → ℚ → ℚ → ℚ
sameCayleySecond c x y =
  inverseDenominator c *
    (((step c * secondCoupling c) * x)
       + ((1ℚ + quarter c * (step c * step c) *
                    (firstCoupling c * secondCoupling c)) * y))

sameCayleyFirstZero : (c : CertifiedCayley) →
  sameCayleyFirst c 0ℚ 0ℚ ≡ 0ℚ
sameCayleyFirstZero c =
  ℚRing.solve-∀
    (step c) (firstCoupling c) (secondCoupling c)
    (inverseDenominator c) (quarter c)

sameCayleySecondZero : (c : CertifiedCayley) →
  sameCayleySecond c 0ℚ 0ℚ ≡ 0ℚ
sameCayleySecondZero c =
  ℚRing.solve-∀
    (step c) (firstCoupling c) (secondCoupling c)
    (inverseDenominator c) (quarter c)

-- Distinct IDs are required for the two-output matrix interpretation.
-- Coincident IDs invoke the earlier priority rule and lose output two.
record DistinctCayleyEdge : Set where
  field
    firstID secondID : Nat
    distinct : Indexed.sameID firstID secondID ≡ false
    coefficients : CertifiedCayley

open DistinctCayleyEdge

sameCayleyPrimitive :
  Nat → Nat → CertifiedCayley → Frame.LocalPrimitive ℚ
sameCayleyPrimitive firstID secondID c =
  Frame.localPrimitive firstID secondID
    (sameCayleyFirst c) (sameCayleySecond c)

sameCayleyZeroPreserving :
  (i j : Nat) (c : CertifiedCayley) →
  Reach.ZeroPreserving 0ℚ (sameCayleyPrimitive i j c)
sameCayleyZeroPreserving i j c = record
  { firstZero = sameCayleyFirstZero c
  ; secondZero = sameCayleySecondZero c
  }

sameCayleyGuarded :
  (i j : Nat) (c : CertifiedCayley) →
  Reach.GuardedPrimitive ℚ 0ℚ
sameCayleyGuarded i j c =
  Reach.guardedPrimitive
    (sameCayleyPrimitive i j c)
    (sameCayleyZeroPreserving i j c)

sameCayleyReachEvent :
  (i j : Nat) (c : CertifiedCayley) →
  Reach.LocalEvent ℚ 0ℚ
sameCayleyReachEvent i j c =
  Reach.propagate (sameCayleyGuarded i j c)

-- Ohmic/relaxation/load steps are diagonal Cayley updates.
-- Their one-coordinate zero-preserving law is separately verified.
record CertifiedDiagonalCayley : Set where
  field
    dampingStep generator inverseDiagonal half : ℚ
    inverseDiagonalLaw :
      (1ℚ - half * (dampingStep * generator)) *
        inverseDiagonal ≡ 1ℚ
    halfIsHalf : half + half ≡ 1ℚ

diagonalCayley : CertifiedDiagonalCayley → ℚ → ℚ
diagonalCayley d x =
  CertifiedDiagonalCayley.inverseDiagonal d *
    ((1ℚ + CertifiedDiagonalCayley.half d *
      (CertifiedDiagonalCayley.dampingStep d *
       CertifiedDiagonalCayley.generator d)) * x)

diagonalCayleyZero : (d : CertifiedDiagonalCayley) →
  diagonalCayley d 0ℚ ≡ 0ℚ
diagonalCayleyZero d =
  ℚRing.solve-∀
    (CertifiedDiagonalCayley.inverseDiagonal d)
    (CertifiedDiagonalCayley.half d)
    (CertifiedDiagonalCayley.dampingStep d)
    (CertifiedDiagonalCayley.generator d)

-- Reuse the selected edge's certified, distinct original IDs
-- instead of allowing the same coordinate as both matrix endpoints.
guardedDistinctCayleyEdge :
  (edge : DistinctCayleyEdge) → Reach.GuardedPrimitive ℚ 0ℚ
guardedDistinctCayleyEdge edge =
  sameCayleyGuarded
    (DistinctCayleyEdge.firstID edge)
    (DistinctCayleyEdge.secondID edge)
    (DistinctCayleyEdge.coefficients edge)

-- The original one-coordinate local damping step is represented as
-- the first output of a two-coordinate frame; second output is an
-- unchanged coordinate. Its endpoint IDs must be distinct.
diagonalFramePrimitive :
  Nat → Nat → CertifiedDiagonalCayley → Frame.LocalPrimitive ℚ
diagonalFramePrimitive i j d =
  Frame.localPrimitive i j
    (λ x y → diagonalCayley d x)
    (λ x y → y)

diagonalFrameZeroPreserving :
  (i j : Nat) (d : CertifiedDiagonalCayley) →
  Reach.ZeroPreserving 0ℚ (diagonalFramePrimitive i j d)
diagonalFrameZeroPreserving i j d = record
  { firstZero = diagonalCayleyZero d
  ; secondZero = refl
  }

diagonalFrameReachEvent :
  (i j : Nat) (d : CertifiedDiagonalCayley) →
  Reach.LocalEvent ℚ 0ℚ
diagonalFrameReachEvent i j d =
  Reach.propagate
    (Reach.guardedPrimitive
      (diagonalFramePrimitive i j d)
      (diagonalFrameZeroPreserving i j d))

-- Explicit SAME-object dependent consumer of the prior all-N theorem.
-- An arbitrary finite list may interleave actual two-coordinate Cayley
-- updates with independently tagged external source/current injections.
-- Its reachability conclusion is conditional on the certified q value,
-- not on any fabricated ambient Sun-Earth energy source.
open import Agda.Builtin.List using (List)

sameCayleySourceCone :
  (events : List (Reach.LocalEvent ℚ 0ℚ))
  (s : Frame.State ℚ) (R : Nat → Set) →
  Reach.OutsideZero 0ℚ s R →
  Reach.OutsideZero 0ℚ
    (Reach.runEvents events s) (Reach.reachEvents events R)
sameCayleySourceCone events s R initial =
  Reach.noSignalOutsideInterleavedSourceCone 0ℚ events s R initial

-- A concrete source-to-Cayley sequence. The source ID is not
-- permitted to appear from a passive Green/Cayley stage: it is
-- injected by an explicit event owned as natural or controller.
open import Agda.Builtin.List using ([]; _∷_)

singleCayleyWithSource :
  Reach.SourceOwner → Nat → (ℚ → ℚ) →
  DistinctCayleyEdge → List (Reach.LocalEvent ℚ 0ℚ)
singleCayleyWithSource owner sourceID source edge =
  Reach.injectAt owner sourceID source ∷
    Reach.propagate (guardedDistinctCayleyEdge edge) ∷ []

singleCayleyWithSourceNoSignalOutsideReach :
  (owner : Reach.SourceOwner)
  (sourceID : Nat) (source : ℚ → ℚ)
  (edge : DistinctCayleyEdge)
  (s : Frame.State ℚ) (R : Nat → Set) →
  Reach.OutsideZero 0ℚ s R →
  Reach.OutsideZero 0ℚ
    (Reach.runEvents (singleCayleyWithSource owner sourceID source edge) s)
    (Reach.reachEvents (singleCayleyWithSource owner sourceID source edge) R)
singleCayleyWithSourceNoSignalOutsideReach
  owner sourceID source edge s R initial =
  Reach.noSignalOutsideInterleavedSourceCone
    0ℚ (singleCayleyWithSource owner sourceID source edge)
    s R initial
