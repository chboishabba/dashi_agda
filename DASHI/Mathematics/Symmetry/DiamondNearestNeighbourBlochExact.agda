module DASHI.Mathematics.Symmetry.DiamondNearestNeighbourBlochExact where

-- Ideal nearest-neighbour spinless two-sublattice diamond Bloch model.
-- Source geometry: DiamondFccPrimitiveGlideExact's infinite A/B FCC
-- carrier; four B neighbours of A(0) at quarter-cell displacements
-- (+,+,+),(+,-,-),(-,+,-),(-,-,+).
-- Classical periodic tight-binding/Fourier/Weyl prior art; this is
-- finite fourth-root phase code and symmetry proof, NOT a calibrated
-- diamond or NV spin/electron/nuclear device Hamiltonian.
--
-- Reuses the same Q4 and Gaussian-Z[i] arithmetic already committed
-- in DiamondEightSiteStructureFactorExact: no duplicate complex ring.
-- Momentum is sampled at integer conventional reciprocal indices:
-- exp(i π/2 * (h dx + k dy + l dz)).
-- Operator H(k) = [[0,Gamma(k)],[conj Gamma(k),0]] is Hermitian;
-- H(k)^2 = |Gamma(k)|^2 * I on this exactly sampled carrier.
-- Source-level proof cases; Agda kernel has not yet been run.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Integer using (ℤ; +_; -_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D
import DASHI.Mathematics.Symmetry.DiamondEightSiteStructureFactorExact as Diff
import DASHI.Mathematics.Symmetry.DiamondFccPrimitiveGlideExact as FCC
import DASHI.Mathematics.Symmetry.TetragonalIntegralLatticeActionExact as C

record K4 : Set where
  constructor k4
  field
    h k l : D.Quarter
open K4 public

-- These actual B sites produce the four tetrahedral neighbour bonds.
neighbour0 neighbour1 neighbour2 neighbour3 : FCC.DiamondSite
neighbour0 = FCC.B (FCC.primitive (+ 0) (+ 0) (+ 0))
neighbour1 = FCC.B (FCC.primitive (- (+ 1)) (+ 0) (+ 0))
neighbour2 = FCC.B (FCC.primitive (+ 0) (- (+ 1)) (+ 0))
neighbour3 = FCC.B (FCC.primitive (+ 0) (+ 0) (- (+ 1)))

neighbour0Position :
  FCC.sitePosition neighbour0 ≡
  C.xyz (+ 1) (+ 1) (+ 1)
neighbour0Position = refl
neighbour1Position :
  FCC.sitePosition neighbour1 ≡
  C.xyz (+ 1) (- (+ 1)) (- (+ 1))
neighbour1Position = refl
neighbour2Position :
  FCC.sitePosition neighbour2 ≡
  C.xyz (- (+ 1)) (+ 1) (- (+ 1))
neighbour2Position = refl
neighbour3Position :
  FCC.sitePosition neighbour3 ≡
  C.xyz (- (+ 1)) (- (+ 1)) (+ 1)
neighbour3Position = refl

-- Sign parity makes the four equal-length bonds a tetrahedron.
-- These are the A->B bonds, not the 8 conventional unit-cell sites.
data Bond4 : Set where
  b0 b1 b2 b3 : Bond4

bondPhase : Bond4 → K4 → D.Quarter
bondPhase b0 (k4 h k l) = D.add h (D.add k l)
bondPhase b1 (k4 h k l) = D.add h (D.add (D.neg k) (D.neg l))
bondPhase b2 (k4 h k l) = D.add (D.neg h) (D.add k (D.neg l))
bondPhase b3 (k4 h k l) = D.add (D.neg h) (D.add (D.neg k) l)

bondAmplitude : Bond4 → K4 → Diff.Gaussian
bondAmplitude b q = Diff.phase (bondPhase b q)

gamma : K4 → Diff.Gaussian
gamma q =
  Diff.gadd
    (Diff.gadd (bondAmplitude b0 q) (bondAmplitude b1 q))
    (Diff.gadd (bondAmplitude b2 q) (bondAmplitude b3 q))

conjugate : Diff.Gaussian → Diff.Gaussian
conjugate (Diff.gaussian a b) = Diff.gaussian a (- b)

-- Hermitian 2 x 2 Bloch matrix. The zero-diagonal and conjugate
-- off-diagonal terms are EXACT; no eigenvalue square-root is assumed.
record Bloch2 : Set where
  constructor bloch2
  field
    aa ab ba bb : Diff.Gaussian
open Bloch2 public

hamiltonian : K4 → Bloch2
hamiltonian q =
  bloch2 Diff.gzero (gamma q) (conjugate (gamma q)) Diff.gzero

squaredGap : K4 → ℤ
squaredGap q = Diff.norm2 (gamma q)

gammaSquareDiagonal : (q : K4) →
  Diff.gmul (ab (hamiltonian q)) (ba (hamiltonian q))
  ≡ Diff.gaussian (squaredGap q) (+ 0)
gammaSquareDiagonal (k4 D.q0 D.q0 D.q0) = refl
gammaSquareDiagonal (k4 D.q0 D.q0 D.q1) = refl
gammaSquareDiagonal (k4 D.q0 D.q0 D.q2) = refl
gammaSquareDiagonal (k4 D.q0 D.q0 D.q3) = refl
gammaSquareDiagonal (k4 D.q0 D.q1 D.q0) = refl
gammaSquareDiagonal (k4 D.q0 D.q1 D.q1) = refl
gammaSquareDiagonal (k4 D.q0 D.q1 D.q2) = refl
gammaSquareDiagonal (k4 D.q0 D.q1 D.q3) = refl
gammaSquareDiagonal (k4 D.q0 D.q2 D.q0) = refl
gammaSquareDiagonal (k4 D.q0 D.q2 D.q1) = refl
gammaSquareDiagonal (k4 D.q0 D.q2 D.q2) = refl
gammaSquareDiagonal (k4 D.q0 D.q2 D.q3) = refl
gammaSquareDiagonal (k4 D.q0 D.q3 D.q0) = refl
gammaSquareDiagonal (k4 D.q0 D.q3 D.q1) = refl
gammaSquareDiagonal (k4 D.q0 D.q3 D.q2) = refl
gammaSquareDiagonal (k4 D.q0 D.q3 D.q3) = refl
gammaSquareDiagonal (k4 D.q1 D.q0 D.q0) = refl
gammaSquareDiagonal (k4 D.q1 D.q0 D.q1) = refl
gammaSquareDiagonal (k4 D.q1 D.q0 D.q2) = refl
gammaSquareDiagonal (k4 D.q1 D.q0 D.q3) = refl
gammaSquareDiagonal (k4 D.q1 D.q1 D.q0) = refl
gammaSquareDiagonal (k4 D.q1 D.q1 D.q1) = refl
gammaSquareDiagonal (k4 D.q1 D.q1 D.q2) = refl
gammaSquareDiagonal (k4 D.q1 D.q1 D.q3) = refl
gammaSquareDiagonal (k4 D.q1 D.q2 D.q0) = refl
gammaSquareDiagonal (k4 D.q1 D.q2 D.q1) = refl
gammaSquareDiagonal (k4 D.q1 D.q2 D.q2) = refl
gammaSquareDiagonal (k4 D.q1 D.q2 D.q3) = refl
gammaSquareDiagonal (k4 D.q1 D.q3 D.q0) = refl
gammaSquareDiagonal (k4 D.q1 D.q3 D.q1) = refl
gammaSquareDiagonal (k4 D.q1 D.q3 D.q2) = refl
gammaSquareDiagonal (k4 D.q1 D.q3 D.q3) = refl
gammaSquareDiagonal (k4 D.q2 D.q0 D.q0) = refl
gammaSquareDiagonal (k4 D.q2 D.q0 D.q1) = refl
gammaSquareDiagonal (k4 D.q2 D.q0 D.q2) = refl
gammaSquareDiagonal (k4 D.q2 D.q0 D.q3) = refl
gammaSquareDiagonal (k4 D.q2 D.q1 D.q0) = refl
gammaSquareDiagonal (k4 D.q2 D.q1 D.q1) = refl
gammaSquareDiagonal (k4 D.q2 D.q1 D.q2) = refl
gammaSquareDiagonal (k4 D.q2 D.q1 D.q3) = refl
gammaSquareDiagonal (k4 D.q2 D.q2 D.q0) = refl
gammaSquareDiagonal (k4 D.q2 D.q2 D.q1) = refl
gammaSquareDiagonal (k4 D.q2 D.q2 D.q2) = refl
gammaSquareDiagonal (k4 D.q2 D.q2 D.q3) = refl
gammaSquareDiagonal (k4 D.q2 D.q3 D.q0) = refl
gammaSquareDiagonal (k4 D.q2 D.q3 D.q1) = refl
gammaSquareDiagonal (k4 D.q2 D.q3 D.q2) = refl
gammaSquareDiagonal (k4 D.q2 D.q3 D.q3) = refl
gammaSquareDiagonal (k4 D.q3 D.q0 D.q0) = refl
gammaSquareDiagonal (k4 D.q3 D.q0 D.q1) = refl
gammaSquareDiagonal (k4 D.q3 D.q0 D.q2) = refl
gammaSquareDiagonal (k4 D.q3 D.q0 D.q3) = refl
gammaSquareDiagonal (k4 D.q3 D.q1 D.q0) = refl
gammaSquareDiagonal (k4 D.q3 D.q1 D.q1) = refl
gammaSquareDiagonal (k4 D.q3 D.q1 D.q2) = refl
gammaSquareDiagonal (k4 D.q3 D.q1 D.q3) = refl
gammaSquareDiagonal (k4 D.q3 D.q2 D.q0) = refl
gammaSquareDiagonal (k4 D.q3 D.q2 D.q1) = refl
gammaSquareDiagonal (k4 D.q3 D.q2 D.q2) = refl
gammaSquareDiagonal (k4 D.q3 D.q2 D.q3) = refl
gammaSquareDiagonal (k4 D.q3 D.q3 D.q0) = refl
gammaSquareDiagonal (k4 D.q3 D.q3 D.q1) = refl
gammaSquareDiagonal (k4 D.q3 D.q3 D.q2) = refl
gammaSquareDiagonal (k4 D.q3 D.q3 D.q3) = refl

gammaSquareDiagonalOpposite : (q : K4) →
  Diff.gmul (ba (hamiltonian q)) (ab (hamiltonian q))
  ≡ Diff.gaussian (squaredGap q) (+ 0)
gammaSquareDiagonalOpposite (k4 D.q0 D.q0 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q0 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q0 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q0 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q1 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q1 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q1 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q1 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q2 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q2 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q2 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q2 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q3 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q3 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q3 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q0 D.q3 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q0 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q0 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q0 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q0 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q1 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q1 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q1 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q1 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q2 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q2 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q2 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q2 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q3 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q3 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q3 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q1 D.q3 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q0 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q0 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q0 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q0 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q1 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q1 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q1 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q1 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q2 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q2 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q2 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q2 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q3 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q3 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q3 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q2 D.q3 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q0 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q0 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q0 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q0 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q1 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q1 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q1 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q1 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q2 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q2 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q2 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q2 D.q3) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q3 D.q0) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q3 D.q1) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q3 D.q2) = refl
gammaSquareDiagonalOpposite (k4 D.q3 D.q3 D.q3) = refl

-- The underlying spatial cubic group is generated by coordinate
-- swaps and sign flips. A sign flip can conjugate Gamma, while
-- permutations leave Gamma unchanged. Either preserves |Gamma|².
flipX flipY flipZ swapXY swapYZ : K4 → K4
flipX (k4 h k l) = k4 (D.neg h) k l
flipY (k4 h k l) = k4 h (D.neg k) l
flipZ (k4 h k l) = k4 h k (D.neg l)
swapXY (k4 h k l) = k4 k h l
swapYZ (k4 h k l) = k4 h l k

gammaSwapXY : (q : K4) → gamma (swapXY q) ≡ gamma q
gammaSwapYZ : (q : K4) → gamma (swapYZ q) ≡ gamma q
gammaFlipX : (q : K4) → gamma (flipX q) ≡ conjugate (gamma q)
gammaFlipY : (q : K4) → gamma (flipY q) ≡ conjugate (gamma q)
gammaFlipZ : (q : K4) → gamma (flipZ q) ≡ conjugate (gamma q)
gammaSwapXY (k4 D.q0 D.q0 D.q0) = refl
gammaSwapXY (k4 D.q0 D.q0 D.q1) = refl
gammaSwapXY (k4 D.q0 D.q0 D.q2) = refl
gammaSwapXY (k4 D.q0 D.q0 D.q3) = refl
gammaSwapXY (k4 D.q0 D.q1 D.q0) = refl
gammaSwapXY (k4 D.q0 D.q1 D.q1) = refl
gammaSwapXY (k4 D.q0 D.q1 D.q2) = refl
gammaSwapXY (k4 D.q0 D.q1 D.q3) = refl
gammaSwapXY (k4 D.q0 D.q2 D.q0) = refl
gammaSwapXY (k4 D.q0 D.q2 D.q1) = refl
gammaSwapXY (k4 D.q0 D.q2 D.q2) = refl
gammaSwapXY (k4 D.q0 D.q2 D.q3) = refl
gammaSwapXY (k4 D.q0 D.q3 D.q0) = refl
gammaSwapXY (k4 D.q0 D.q3 D.q1) = refl
gammaSwapXY (k4 D.q0 D.q3 D.q2) = refl
gammaSwapXY (k4 D.q0 D.q3 D.q3) = refl
gammaSwapXY (k4 D.q1 D.q0 D.q0) = refl
gammaSwapXY (k4 D.q1 D.q0 D.q1) = refl
gammaSwapXY (k4 D.q1 D.q0 D.q2) = refl
gammaSwapXY (k4 D.q1 D.q0 D.q3) = refl
gammaSwapXY (k4 D.q1 D.q1 D.q0) = refl
gammaSwapXY (k4 D.q1 D.q1 D.q1) = refl
gammaSwapXY (k4 D.q1 D.q1 D.q2) = refl
gammaSwapXY (k4 D.q1 D.q1 D.q3) = refl
gammaSwapXY (k4 D.q1 D.q2 D.q0) = refl
gammaSwapXY (k4 D.q1 D.q2 D.q1) = refl
gammaSwapXY (k4 D.q1 D.q2 D.q2) = refl
gammaSwapXY (k4 D.q1 D.q2 D.q3) = refl
gammaSwapXY (k4 D.q1 D.q3 D.q0) = refl
gammaSwapXY (k4 D.q1 D.q3 D.q1) = refl
gammaSwapXY (k4 D.q1 D.q3 D.q2) = refl
gammaSwapXY (k4 D.q1 D.q3 D.q3) = refl
gammaSwapXY (k4 D.q2 D.q0 D.q0) = refl
gammaSwapXY (k4 D.q2 D.q0 D.q1) = refl
gammaSwapXY (k4 D.q2 D.q0 D.q2) = refl
gammaSwapXY (k4 D.q2 D.q0 D.q3) = refl
gammaSwapXY (k4 D.q2 D.q1 D.q0) = refl
gammaSwapXY (k4 D.q2 D.q1 D.q1) = refl
gammaSwapXY (k4 D.q2 D.q1 D.q2) = refl
gammaSwapXY (k4 D.q2 D.q1 D.q3) = refl
gammaSwapXY (k4 D.q2 D.q2 D.q0) = refl
gammaSwapXY (k4 D.q2 D.q2 D.q1) = refl
gammaSwapXY (k4 D.q2 D.q2 D.q2) = refl
gammaSwapXY (k4 D.q2 D.q2 D.q3) = refl
gammaSwapXY (k4 D.q2 D.q3 D.q0) = refl
gammaSwapXY (k4 D.q2 D.q3 D.q1) = refl
gammaSwapXY (k4 D.q2 D.q3 D.q2) = refl
gammaSwapXY (k4 D.q2 D.q3 D.q3) = refl
gammaSwapXY (k4 D.q3 D.q0 D.q0) = refl
gammaSwapXY (k4 D.q3 D.q0 D.q1) = refl
gammaSwapXY (k4 D.q3 D.q0 D.q2) = refl
gammaSwapXY (k4 D.q3 D.q0 D.q3) = refl
gammaSwapXY (k4 D.q3 D.q1 D.q0) = refl
gammaSwapXY (k4 D.q3 D.q1 D.q1) = refl
gammaSwapXY (k4 D.q3 D.q1 D.q2) = refl
gammaSwapXY (k4 D.q3 D.q1 D.q3) = refl
gammaSwapXY (k4 D.q3 D.q2 D.q0) = refl
gammaSwapXY (k4 D.q3 D.q2 D.q1) = refl
gammaSwapXY (k4 D.q3 D.q2 D.q2) = refl
gammaSwapXY (k4 D.q3 D.q2 D.q3) = refl
gammaSwapXY (k4 D.q3 D.q3 D.q0) = refl
gammaSwapXY (k4 D.q3 D.q3 D.q1) = refl
gammaSwapXY (k4 D.q3 D.q3 D.q2) = refl
gammaSwapXY (k4 D.q3 D.q3 D.q3) = refl
gammaSwapYZ (k4 D.q0 D.q0 D.q0) = refl
gammaSwapYZ (k4 D.q0 D.q0 D.q1) = refl
gammaSwapYZ (k4 D.q0 D.q0 D.q2) = refl
gammaSwapYZ (k4 D.q0 D.q0 D.q3) = refl
gammaSwapYZ (k4 D.q0 D.q1 D.q0) = refl
gammaSwapYZ (k4 D.q0 D.q1 D.q1) = refl
gammaSwapYZ (k4 D.q0 D.q1 D.q2) = refl
gammaSwapYZ (k4 D.q0 D.q1 D.q3) = refl
gammaSwapYZ (k4 D.q0 D.q2 D.q0) = refl
gammaSwapYZ (k4 D.q0 D.q2 D.q1) = refl
gammaSwapYZ (k4 D.q0 D.q2 D.q2) = refl
gammaSwapYZ (k4 D.q0 D.q2 D.q3) = refl
gammaSwapYZ (k4 D.q0 D.q3 D.q0) = refl
gammaSwapYZ (k4 D.q0 D.q3 D.q1) = refl
gammaSwapYZ (k4 D.q0 D.q3 D.q2) = refl
gammaSwapYZ (k4 D.q0 D.q3 D.q3) = refl
gammaSwapYZ (k4 D.q1 D.q0 D.q0) = refl
gammaSwapYZ (k4 D.q1 D.q0 D.q1) = refl
gammaSwapYZ (k4 D.q1 D.q0 D.q2) = refl
gammaSwapYZ (k4 D.q1 D.q0 D.q3) = refl
gammaSwapYZ (k4 D.q1 D.q1 D.q0) = refl
gammaSwapYZ (k4 D.q1 D.q1 D.q1) = refl
gammaSwapYZ (k4 D.q1 D.q1 D.q2) = refl
gammaSwapYZ (k4 D.q1 D.q1 D.q3) = refl
gammaSwapYZ (k4 D.q1 D.q2 D.q0) = refl
gammaSwapYZ (k4 D.q1 D.q2 D.q1) = refl
gammaSwapYZ (k4 D.q1 D.q2 D.q2) = refl
gammaSwapYZ (k4 D.q1 D.q2 D.q3) = refl
gammaSwapYZ (k4 D.q1 D.q3 D.q0) = refl
gammaSwapYZ (k4 D.q1 D.q3 D.q1) = refl
gammaSwapYZ (k4 D.q1 D.q3 D.q2) = refl
gammaSwapYZ (k4 D.q1 D.q3 D.q3) = refl
gammaSwapYZ (k4 D.q2 D.q0 D.q0) = refl
gammaSwapYZ (k4 D.q2 D.q0 D.q1) = refl
gammaSwapYZ (k4 D.q2 D.q0 D.q2) = refl
gammaSwapYZ (k4 D.q2 D.q0 D.q3) = refl
gammaSwapYZ (k4 D.q2 D.q1 D.q0) = refl
gammaSwapYZ (k4 D.q2 D.q1 D.q1) = refl
gammaSwapYZ (k4 D.q2 D.q1 D.q2) = refl
gammaSwapYZ (k4 D.q2 D.q1 D.q3) = refl
gammaSwapYZ (k4 D.q2 D.q2 D.q0) = refl
gammaSwapYZ (k4 D.q2 D.q2 D.q1) = refl
gammaSwapYZ (k4 D.q2 D.q2 D.q2) = refl
gammaSwapYZ (k4 D.q2 D.q2 D.q3) = refl
gammaSwapYZ (k4 D.q2 D.q3 D.q0) = refl
gammaSwapYZ (k4 D.q2 D.q3 D.q1) = refl
gammaSwapYZ (k4 D.q2 D.q3 D.q2) = refl
gammaSwapYZ (k4 D.q2 D.q3 D.q3) = refl
gammaSwapYZ (k4 D.q3 D.q0 D.q0) = refl
gammaSwapYZ (k4 D.q3 D.q0 D.q1) = refl
gammaSwapYZ (k4 D.q3 D.q0 D.q2) = refl
gammaSwapYZ (k4 D.q3 D.q0 D.q3) = refl
gammaSwapYZ (k4 D.q3 D.q1 D.q0) = refl
gammaSwapYZ (k4 D.q3 D.q1 D.q1) = refl
gammaSwapYZ (k4 D.q3 D.q1 D.q2) = refl
gammaSwapYZ (k4 D.q3 D.q1 D.q3) = refl
gammaSwapYZ (k4 D.q3 D.q2 D.q0) = refl
gammaSwapYZ (k4 D.q3 D.q2 D.q1) = refl
gammaSwapYZ (k4 D.q3 D.q2 D.q2) = refl
gammaSwapYZ (k4 D.q3 D.q2 D.q3) = refl
gammaSwapYZ (k4 D.q3 D.q3 D.q0) = refl
gammaSwapYZ (k4 D.q3 D.q3 D.q1) = refl
gammaSwapYZ (k4 D.q3 D.q3 D.q2) = refl
gammaSwapYZ (k4 D.q3 D.q3 D.q3) = refl
gammaFlipX (k4 D.q0 D.q0 D.q0) = refl
gammaFlipX (k4 D.q0 D.q0 D.q1) = refl
gammaFlipX (k4 D.q0 D.q0 D.q2) = refl
gammaFlipX (k4 D.q0 D.q0 D.q3) = refl
gammaFlipX (k4 D.q0 D.q1 D.q0) = refl
gammaFlipX (k4 D.q0 D.q1 D.q1) = refl
gammaFlipX (k4 D.q0 D.q1 D.q2) = refl
gammaFlipX (k4 D.q0 D.q1 D.q3) = refl
gammaFlipX (k4 D.q0 D.q2 D.q0) = refl
gammaFlipX (k4 D.q0 D.q2 D.q1) = refl
gammaFlipX (k4 D.q0 D.q2 D.q2) = refl
gammaFlipX (k4 D.q0 D.q2 D.q3) = refl
gammaFlipX (k4 D.q0 D.q3 D.q0) = refl
gammaFlipX (k4 D.q0 D.q3 D.q1) = refl
gammaFlipX (k4 D.q0 D.q3 D.q2) = refl
gammaFlipX (k4 D.q0 D.q3 D.q3) = refl
gammaFlipX (k4 D.q1 D.q0 D.q0) = refl
gammaFlipX (k4 D.q1 D.q0 D.q1) = refl
gammaFlipX (k4 D.q1 D.q0 D.q2) = refl
gammaFlipX (k4 D.q1 D.q0 D.q3) = refl
gammaFlipX (k4 D.q1 D.q1 D.q0) = refl
gammaFlipX (k4 D.q1 D.q1 D.q1) = refl
gammaFlipX (k4 D.q1 D.q1 D.q2) = refl
gammaFlipX (k4 D.q1 D.q1 D.q3) = refl
gammaFlipX (k4 D.q1 D.q2 D.q0) = refl
gammaFlipX (k4 D.q1 D.q2 D.q1) = refl
gammaFlipX (k4 D.q1 D.q2 D.q2) = refl
gammaFlipX (k4 D.q1 D.q2 D.q3) = refl
gammaFlipX (k4 D.q1 D.q3 D.q0) = refl
gammaFlipX (k4 D.q1 D.q3 D.q1) = refl
gammaFlipX (k4 D.q1 D.q3 D.q2) = refl
gammaFlipX (k4 D.q1 D.q3 D.q3) = refl
gammaFlipX (k4 D.q2 D.q0 D.q0) = refl
gammaFlipX (k4 D.q2 D.q0 D.q1) = refl
gammaFlipX (k4 D.q2 D.q0 D.q2) = refl
gammaFlipX (k4 D.q2 D.q0 D.q3) = refl
gammaFlipX (k4 D.q2 D.q1 D.q0) = refl
gammaFlipX (k4 D.q2 D.q1 D.q1) = refl
gammaFlipX (k4 D.q2 D.q1 D.q2) = refl
gammaFlipX (k4 D.q2 D.q1 D.q3) = refl
gammaFlipX (k4 D.q2 D.q2 D.q0) = refl
gammaFlipX (k4 D.q2 D.q2 D.q1) = refl
gammaFlipX (k4 D.q2 D.q2 D.q2) = refl
gammaFlipX (k4 D.q2 D.q2 D.q3) = refl
gammaFlipX (k4 D.q2 D.q3 D.q0) = refl
gammaFlipX (k4 D.q2 D.q3 D.q1) = refl
gammaFlipX (k4 D.q2 D.q3 D.q2) = refl
gammaFlipX (k4 D.q2 D.q3 D.q3) = refl
gammaFlipX (k4 D.q3 D.q0 D.q0) = refl
gammaFlipX (k4 D.q3 D.q0 D.q1) = refl
gammaFlipX (k4 D.q3 D.q0 D.q2) = refl
gammaFlipX (k4 D.q3 D.q0 D.q3) = refl
gammaFlipX (k4 D.q3 D.q1 D.q0) = refl
gammaFlipX (k4 D.q3 D.q1 D.q1) = refl
gammaFlipX (k4 D.q3 D.q1 D.q2) = refl
gammaFlipX (k4 D.q3 D.q1 D.q3) = refl
gammaFlipX (k4 D.q3 D.q2 D.q0) = refl
gammaFlipX (k4 D.q3 D.q2 D.q1) = refl
gammaFlipX (k4 D.q3 D.q2 D.q2) = refl
gammaFlipX (k4 D.q3 D.q2 D.q3) = refl
gammaFlipX (k4 D.q3 D.q3 D.q0) = refl
gammaFlipX (k4 D.q3 D.q3 D.q1) = refl
gammaFlipX (k4 D.q3 D.q3 D.q2) = refl
gammaFlipX (k4 D.q3 D.q3 D.q3) = refl
gammaFlipY (k4 D.q0 D.q0 D.q0) = refl
gammaFlipY (k4 D.q0 D.q0 D.q1) = refl
gammaFlipY (k4 D.q0 D.q0 D.q2) = refl
gammaFlipY (k4 D.q0 D.q0 D.q3) = refl
gammaFlipY (k4 D.q0 D.q1 D.q0) = refl
gammaFlipY (k4 D.q0 D.q1 D.q1) = refl
gammaFlipY (k4 D.q0 D.q1 D.q2) = refl
gammaFlipY (k4 D.q0 D.q1 D.q3) = refl
gammaFlipY (k4 D.q0 D.q2 D.q0) = refl
gammaFlipY (k4 D.q0 D.q2 D.q1) = refl
gammaFlipY (k4 D.q0 D.q2 D.q2) = refl
gammaFlipY (k4 D.q0 D.q2 D.q3) = refl
gammaFlipY (k4 D.q0 D.q3 D.q0) = refl
gammaFlipY (k4 D.q0 D.q3 D.q1) = refl
gammaFlipY (k4 D.q0 D.q3 D.q2) = refl
gammaFlipY (k4 D.q0 D.q3 D.q3) = refl
gammaFlipY (k4 D.q1 D.q0 D.q0) = refl
gammaFlipY (k4 D.q1 D.q0 D.q1) = refl
gammaFlipY (k4 D.q1 D.q0 D.q2) = refl
gammaFlipY (k4 D.q1 D.q0 D.q3) = refl
gammaFlipY (k4 D.q1 D.q1 D.q0) = refl
gammaFlipY (k4 D.q1 D.q1 D.q1) = refl
gammaFlipY (k4 D.q1 D.q1 D.q2) = refl
gammaFlipY (k4 D.q1 D.q1 D.q3) = refl
gammaFlipY (k4 D.q1 D.q2 D.q0) = refl
gammaFlipY (k4 D.q1 D.q2 D.q1) = refl
gammaFlipY (k4 D.q1 D.q2 D.q2) = refl
gammaFlipY (k4 D.q1 D.q2 D.q3) = refl
gammaFlipY (k4 D.q1 D.q3 D.q0) = refl
gammaFlipY (k4 D.q1 D.q3 D.q1) = refl
gammaFlipY (k4 D.q1 D.q3 D.q2) = refl
gammaFlipY (k4 D.q1 D.q3 D.q3) = refl
gammaFlipY (k4 D.q2 D.q0 D.q0) = refl
gammaFlipY (k4 D.q2 D.q0 D.q1) = refl
gammaFlipY (k4 D.q2 D.q0 D.q2) = refl
gammaFlipY (k4 D.q2 D.q0 D.q3) = refl
gammaFlipY (k4 D.q2 D.q1 D.q0) = refl
gammaFlipY (k4 D.q2 D.q1 D.q1) = refl
gammaFlipY (k4 D.q2 D.q1 D.q2) = refl
gammaFlipY (k4 D.q2 D.q1 D.q3) = refl
gammaFlipY (k4 D.q2 D.q2 D.q0) = refl
gammaFlipY (k4 D.q2 D.q2 D.q1) = refl
gammaFlipY (k4 D.q2 D.q2 D.q2) = refl
gammaFlipY (k4 D.q2 D.q2 D.q3) = refl
gammaFlipY (k4 D.q2 D.q3 D.q0) = refl
gammaFlipY (k4 D.q2 D.q3 D.q1) = refl
gammaFlipY (k4 D.q2 D.q3 D.q2) = refl
gammaFlipY (k4 D.q2 D.q3 D.q3) = refl
gammaFlipY (k4 D.q3 D.q0 D.q0) = refl
gammaFlipY (k4 D.q3 D.q0 D.q1) = refl
gammaFlipY (k4 D.q3 D.q0 D.q2) = refl
gammaFlipY (k4 D.q3 D.q0 D.q3) = refl
gammaFlipY (k4 D.q3 D.q1 D.q0) = refl
gammaFlipY (k4 D.q3 D.q1 D.q1) = refl
gammaFlipY (k4 D.q3 D.q1 D.q2) = refl
gammaFlipY (k4 D.q3 D.q1 D.q3) = refl
gammaFlipY (k4 D.q3 D.q2 D.q0) = refl
gammaFlipY (k4 D.q3 D.q2 D.q1) = refl
gammaFlipY (k4 D.q3 D.q2 D.q2) = refl
gammaFlipY (k4 D.q3 D.q2 D.q3) = refl
gammaFlipY (k4 D.q3 D.q3 D.q0) = refl
gammaFlipY (k4 D.q3 D.q3 D.q1) = refl
gammaFlipY (k4 D.q3 D.q3 D.q2) = refl
gammaFlipY (k4 D.q3 D.q3 D.q3) = refl
gammaFlipZ (k4 D.q0 D.q0 D.q0) = refl
gammaFlipZ (k4 D.q0 D.q0 D.q1) = refl
gammaFlipZ (k4 D.q0 D.q0 D.q2) = refl
gammaFlipZ (k4 D.q0 D.q0 D.q3) = refl
gammaFlipZ (k4 D.q0 D.q1 D.q0) = refl
gammaFlipZ (k4 D.q0 D.q1 D.q1) = refl
gammaFlipZ (k4 D.q0 D.q1 D.q2) = refl
gammaFlipZ (k4 D.q0 D.q1 D.q3) = refl
gammaFlipZ (k4 D.q0 D.q2 D.q0) = refl
gammaFlipZ (k4 D.q0 D.q2 D.q1) = refl
gammaFlipZ (k4 D.q0 D.q2 D.q2) = refl
gammaFlipZ (k4 D.q0 D.q2 D.q3) = refl
gammaFlipZ (k4 D.q0 D.q3 D.q0) = refl
gammaFlipZ (k4 D.q0 D.q3 D.q1) = refl
gammaFlipZ (k4 D.q0 D.q3 D.q2) = refl
gammaFlipZ (k4 D.q0 D.q3 D.q3) = refl
gammaFlipZ (k4 D.q1 D.q0 D.q0) = refl
gammaFlipZ (k4 D.q1 D.q0 D.q1) = refl
gammaFlipZ (k4 D.q1 D.q0 D.q2) = refl
gammaFlipZ (k4 D.q1 D.q0 D.q3) = refl
gammaFlipZ (k4 D.q1 D.q1 D.q0) = refl
gammaFlipZ (k4 D.q1 D.q1 D.q1) = refl
gammaFlipZ (k4 D.q1 D.q1 D.q2) = refl
gammaFlipZ (k4 D.q1 D.q1 D.q3) = refl
gammaFlipZ (k4 D.q1 D.q2 D.q0) = refl
gammaFlipZ (k4 D.q1 D.q2 D.q1) = refl
gammaFlipZ (k4 D.q1 D.q2 D.q2) = refl
gammaFlipZ (k4 D.q1 D.q2 D.q3) = refl
gammaFlipZ (k4 D.q1 D.q3 D.q0) = refl
gammaFlipZ (k4 D.q1 D.q3 D.q1) = refl
gammaFlipZ (k4 D.q1 D.q3 D.q2) = refl
gammaFlipZ (k4 D.q1 D.q3 D.q3) = refl
gammaFlipZ (k4 D.q2 D.q0 D.q0) = refl
gammaFlipZ (k4 D.q2 D.q0 D.q1) = refl
gammaFlipZ (k4 D.q2 D.q0 D.q2) = refl
gammaFlipZ (k4 D.q2 D.q0 D.q3) = refl
gammaFlipZ (k4 D.q2 D.q1 D.q0) = refl
gammaFlipZ (k4 D.q2 D.q1 D.q1) = refl
gammaFlipZ (k4 D.q2 D.q1 D.q2) = refl
gammaFlipZ (k4 D.q2 D.q1 D.q3) = refl
gammaFlipZ (k4 D.q2 D.q2 D.q0) = refl
gammaFlipZ (k4 D.q2 D.q2 D.q1) = refl
gammaFlipZ (k4 D.q2 D.q2 D.q2) = refl
gammaFlipZ (k4 D.q2 D.q2 D.q3) = refl
gammaFlipZ (k4 D.q2 D.q3 D.q0) = refl
gammaFlipZ (k4 D.q2 D.q3 D.q1) = refl
gammaFlipZ (k4 D.q2 D.q3 D.q2) = refl
gammaFlipZ (k4 D.q2 D.q3 D.q3) = refl
gammaFlipZ (k4 D.q3 D.q0 D.q0) = refl
gammaFlipZ (k4 D.q3 D.q0 D.q1) = refl
gammaFlipZ (k4 D.q3 D.q0 D.q2) = refl
gammaFlipZ (k4 D.q3 D.q0 D.q3) = refl
gammaFlipZ (k4 D.q3 D.q1 D.q0) = refl
gammaFlipZ (k4 D.q3 D.q1 D.q1) = refl
gammaFlipZ (k4 D.q3 D.q1 D.q2) = refl
gammaFlipZ (k4 D.q3 D.q1 D.q3) = refl
gammaFlipZ (k4 D.q3 D.q2 D.q0) = refl
gammaFlipZ (k4 D.q3 D.q2 D.q1) = refl
gammaFlipZ (k4 D.q3 D.q2 D.q2) = refl
gammaFlipZ (k4 D.q3 D.q2 D.q3) = refl
gammaFlipZ (k4 D.q3 D.q3 D.q0) = refl
gammaFlipZ (k4 D.q3 D.q3 D.q1) = refl
gammaFlipZ (k4 D.q3 D.q3 D.q2) = refl
gammaFlipZ (k4 D.q3 D.q3 D.q3) = refl

normSwapXY : (q : K4) → squaredGap (swapXY q) ≡ squaredGap q
normSwapYZ : (q : K4) → squaredGap (swapYZ q) ≡ squaredGap q
normFlipX : (q : K4) → squaredGap (flipX q) ≡ squaredGap q
normFlipY : (q : K4) → squaredGap (flipY q) ≡ squaredGap q
normFlipZ : (q : K4) → squaredGap (flipZ q) ≡ squaredGap q
normSwapXY (k4 D.q0 D.q0 D.q0) = refl
normSwapXY (k4 D.q0 D.q0 D.q1) = refl
normSwapXY (k4 D.q0 D.q0 D.q2) = refl
normSwapXY (k4 D.q0 D.q0 D.q3) = refl
normSwapXY (k4 D.q0 D.q1 D.q0) = refl
normSwapXY (k4 D.q0 D.q1 D.q1) = refl
normSwapXY (k4 D.q0 D.q1 D.q2) = refl
normSwapXY (k4 D.q0 D.q1 D.q3) = refl
normSwapXY (k4 D.q0 D.q2 D.q0) = refl
normSwapXY (k4 D.q0 D.q2 D.q1) = refl
normSwapXY (k4 D.q0 D.q2 D.q2) = refl
normSwapXY (k4 D.q0 D.q2 D.q3) = refl
normSwapXY (k4 D.q0 D.q3 D.q0) = refl
normSwapXY (k4 D.q0 D.q3 D.q1) = refl
normSwapXY (k4 D.q0 D.q3 D.q2) = refl
normSwapXY (k4 D.q0 D.q3 D.q3) = refl
normSwapXY (k4 D.q1 D.q0 D.q0) = refl
normSwapXY (k4 D.q1 D.q0 D.q1) = refl
normSwapXY (k4 D.q1 D.q0 D.q2) = refl
normSwapXY (k4 D.q1 D.q0 D.q3) = refl
normSwapXY (k4 D.q1 D.q1 D.q0) = refl
normSwapXY (k4 D.q1 D.q1 D.q1) = refl
normSwapXY (k4 D.q1 D.q1 D.q2) = refl
normSwapXY (k4 D.q1 D.q1 D.q3) = refl
normSwapXY (k4 D.q1 D.q2 D.q0) = refl
normSwapXY (k4 D.q1 D.q2 D.q1) = refl
normSwapXY (k4 D.q1 D.q2 D.q2) = refl
normSwapXY (k4 D.q1 D.q2 D.q3) = refl
normSwapXY (k4 D.q1 D.q3 D.q0) = refl
normSwapXY (k4 D.q1 D.q3 D.q1) = refl
normSwapXY (k4 D.q1 D.q3 D.q2) = refl
normSwapXY (k4 D.q1 D.q3 D.q3) = refl
normSwapXY (k4 D.q2 D.q0 D.q0) = refl
normSwapXY (k4 D.q2 D.q0 D.q1) = refl
normSwapXY (k4 D.q2 D.q0 D.q2) = refl
normSwapXY (k4 D.q2 D.q0 D.q3) = refl
normSwapXY (k4 D.q2 D.q1 D.q0) = refl
normSwapXY (k4 D.q2 D.q1 D.q1) = refl
normSwapXY (k4 D.q2 D.q1 D.q2) = refl
normSwapXY (k4 D.q2 D.q1 D.q3) = refl
normSwapXY (k4 D.q2 D.q2 D.q0) = refl
normSwapXY (k4 D.q2 D.q2 D.q1) = refl
normSwapXY (k4 D.q2 D.q2 D.q2) = refl
normSwapXY (k4 D.q2 D.q2 D.q3) = refl
normSwapXY (k4 D.q2 D.q3 D.q0) = refl
normSwapXY (k4 D.q2 D.q3 D.q1) = refl
normSwapXY (k4 D.q2 D.q3 D.q2) = refl
normSwapXY (k4 D.q2 D.q3 D.q3) = refl
normSwapXY (k4 D.q3 D.q0 D.q0) = refl
normSwapXY (k4 D.q3 D.q0 D.q1) = refl
normSwapXY (k4 D.q3 D.q0 D.q2) = refl
normSwapXY (k4 D.q3 D.q0 D.q3) = refl
normSwapXY (k4 D.q3 D.q1 D.q0) = refl
normSwapXY (k4 D.q3 D.q1 D.q1) = refl
normSwapXY (k4 D.q3 D.q1 D.q2) = refl
normSwapXY (k4 D.q3 D.q1 D.q3) = refl
normSwapXY (k4 D.q3 D.q2 D.q0) = refl
normSwapXY (k4 D.q3 D.q2 D.q1) = refl
normSwapXY (k4 D.q3 D.q2 D.q2) = refl
normSwapXY (k4 D.q3 D.q2 D.q3) = refl
normSwapXY (k4 D.q3 D.q3 D.q0) = refl
normSwapXY (k4 D.q3 D.q3 D.q1) = refl
normSwapXY (k4 D.q3 D.q3 D.q2) = refl
normSwapXY (k4 D.q3 D.q3 D.q3) = refl
normSwapYZ (k4 D.q0 D.q0 D.q0) = refl
normSwapYZ (k4 D.q0 D.q0 D.q1) = refl
normSwapYZ (k4 D.q0 D.q0 D.q2) = refl
normSwapYZ (k4 D.q0 D.q0 D.q3) = refl
normSwapYZ (k4 D.q0 D.q1 D.q0) = refl
normSwapYZ (k4 D.q0 D.q1 D.q1) = refl
normSwapYZ (k4 D.q0 D.q1 D.q2) = refl
normSwapYZ (k4 D.q0 D.q1 D.q3) = refl
normSwapYZ (k4 D.q0 D.q2 D.q0) = refl
normSwapYZ (k4 D.q0 D.q2 D.q1) = refl
normSwapYZ (k4 D.q0 D.q2 D.q2) = refl
normSwapYZ (k4 D.q0 D.q2 D.q3) = refl
normSwapYZ (k4 D.q0 D.q3 D.q0) = refl
normSwapYZ (k4 D.q0 D.q3 D.q1) = refl
normSwapYZ (k4 D.q0 D.q3 D.q2) = refl
normSwapYZ (k4 D.q0 D.q3 D.q3) = refl
normSwapYZ (k4 D.q1 D.q0 D.q0) = refl
normSwapYZ (k4 D.q1 D.q0 D.q1) = refl
normSwapYZ (k4 D.q1 D.q0 D.q2) = refl
normSwapYZ (k4 D.q1 D.q0 D.q3) = refl
normSwapYZ (k4 D.q1 D.q1 D.q0) = refl
normSwapYZ (k4 D.q1 D.q1 D.q1) = refl
normSwapYZ (k4 D.q1 D.q1 D.q2) = refl
normSwapYZ (k4 D.q1 D.q1 D.q3) = refl
normSwapYZ (k4 D.q1 D.q2 D.q0) = refl
normSwapYZ (k4 D.q1 D.q2 D.q1) = refl
normSwapYZ (k4 D.q1 D.q2 D.q2) = refl
normSwapYZ (k4 D.q1 D.q2 D.q3) = refl
normSwapYZ (k4 D.q1 D.q3 D.q0) = refl
normSwapYZ (k4 D.q1 D.q3 D.q1) = refl
normSwapYZ (k4 D.q1 D.q3 D.q2) = refl
normSwapYZ (k4 D.q1 D.q3 D.q3) = refl
normSwapYZ (k4 D.q2 D.q0 D.q0) = refl
normSwapYZ (k4 D.q2 D.q0 D.q1) = refl
normSwapYZ (k4 D.q2 D.q0 D.q2) = refl
normSwapYZ (k4 D.q2 D.q0 D.q3) = refl
normSwapYZ (k4 D.q2 D.q1 D.q0) = refl
normSwapYZ (k4 D.q2 D.q1 D.q1) = refl
normSwapYZ (k4 D.q2 D.q1 D.q2) = refl
normSwapYZ (k4 D.q2 D.q1 D.q3) = refl
normSwapYZ (k4 D.q2 D.q2 D.q0) = refl
normSwapYZ (k4 D.q2 D.q2 D.q1) = refl
normSwapYZ (k4 D.q2 D.q2 D.q2) = refl
normSwapYZ (k4 D.q2 D.q2 D.q3) = refl
normSwapYZ (k4 D.q2 D.q3 D.q0) = refl
normSwapYZ (k4 D.q2 D.q3 D.q1) = refl
normSwapYZ (k4 D.q2 D.q3 D.q2) = refl
normSwapYZ (k4 D.q2 D.q3 D.q3) = refl
normSwapYZ (k4 D.q3 D.q0 D.q0) = refl
normSwapYZ (k4 D.q3 D.q0 D.q1) = refl
normSwapYZ (k4 D.q3 D.q0 D.q2) = refl
normSwapYZ (k4 D.q3 D.q0 D.q3) = refl
normSwapYZ (k4 D.q3 D.q1 D.q0) = refl
normSwapYZ (k4 D.q3 D.q1 D.q1) = refl
normSwapYZ (k4 D.q3 D.q1 D.q2) = refl
normSwapYZ (k4 D.q3 D.q1 D.q3) = refl
normSwapYZ (k4 D.q3 D.q2 D.q0) = refl
normSwapYZ (k4 D.q3 D.q2 D.q1) = refl
normSwapYZ (k4 D.q3 D.q2 D.q2) = refl
normSwapYZ (k4 D.q3 D.q2 D.q3) = refl
normSwapYZ (k4 D.q3 D.q3 D.q0) = refl
normSwapYZ (k4 D.q3 D.q3 D.q1) = refl
normSwapYZ (k4 D.q3 D.q3 D.q2) = refl
normSwapYZ (k4 D.q3 D.q3 D.q3) = refl
normFlipX (k4 D.q0 D.q0 D.q0) = refl
normFlipX (k4 D.q0 D.q0 D.q1) = refl
normFlipX (k4 D.q0 D.q0 D.q2) = refl
normFlipX (k4 D.q0 D.q0 D.q3) = refl
normFlipX (k4 D.q0 D.q1 D.q0) = refl
normFlipX (k4 D.q0 D.q1 D.q1) = refl
normFlipX (k4 D.q0 D.q1 D.q2) = refl
normFlipX (k4 D.q0 D.q1 D.q3) = refl
normFlipX (k4 D.q0 D.q2 D.q0) = refl
normFlipX (k4 D.q0 D.q2 D.q1) = refl
normFlipX (k4 D.q0 D.q2 D.q2) = refl
normFlipX (k4 D.q0 D.q2 D.q3) = refl
normFlipX (k4 D.q0 D.q3 D.q0) = refl
normFlipX (k4 D.q0 D.q3 D.q1) = refl
normFlipX (k4 D.q0 D.q3 D.q2) = refl
normFlipX (k4 D.q0 D.q3 D.q3) = refl
normFlipX (k4 D.q1 D.q0 D.q0) = refl
normFlipX (k4 D.q1 D.q0 D.q1) = refl
normFlipX (k4 D.q1 D.q0 D.q2) = refl
normFlipX (k4 D.q1 D.q0 D.q3) = refl
normFlipX (k4 D.q1 D.q1 D.q0) = refl
normFlipX (k4 D.q1 D.q1 D.q1) = refl
normFlipX (k4 D.q1 D.q1 D.q2) = refl
normFlipX (k4 D.q1 D.q1 D.q3) = refl
normFlipX (k4 D.q1 D.q2 D.q0) = refl
normFlipX (k4 D.q1 D.q2 D.q1) = refl
normFlipX (k4 D.q1 D.q2 D.q2) = refl
normFlipX (k4 D.q1 D.q2 D.q3) = refl
normFlipX (k4 D.q1 D.q3 D.q0) = refl
normFlipX (k4 D.q1 D.q3 D.q1) = refl
normFlipX (k4 D.q1 D.q3 D.q2) = refl
normFlipX (k4 D.q1 D.q3 D.q3) = refl
normFlipX (k4 D.q2 D.q0 D.q0) = refl
normFlipX (k4 D.q2 D.q0 D.q1) = refl
normFlipX (k4 D.q2 D.q0 D.q2) = refl
normFlipX (k4 D.q2 D.q0 D.q3) = refl
normFlipX (k4 D.q2 D.q1 D.q0) = refl
normFlipX (k4 D.q2 D.q1 D.q1) = refl
normFlipX (k4 D.q2 D.q1 D.q2) = refl
normFlipX (k4 D.q2 D.q1 D.q3) = refl
normFlipX (k4 D.q2 D.q2 D.q0) = refl
normFlipX (k4 D.q2 D.q2 D.q1) = refl
normFlipX (k4 D.q2 D.q2 D.q2) = refl
normFlipX (k4 D.q2 D.q2 D.q3) = refl
normFlipX (k4 D.q2 D.q3 D.q0) = refl
normFlipX (k4 D.q2 D.q3 D.q1) = refl
normFlipX (k4 D.q2 D.q3 D.q2) = refl
normFlipX (k4 D.q2 D.q3 D.q3) = refl
normFlipX (k4 D.q3 D.q0 D.q0) = refl
normFlipX (k4 D.q3 D.q0 D.q1) = refl
normFlipX (k4 D.q3 D.q0 D.q2) = refl
normFlipX (k4 D.q3 D.q0 D.q3) = refl
normFlipX (k4 D.q3 D.q1 D.q0) = refl
normFlipX (k4 D.q3 D.q1 D.q1) = refl
normFlipX (k4 D.q3 D.q1 D.q2) = refl
normFlipX (k4 D.q3 D.q1 D.q3) = refl
normFlipX (k4 D.q3 D.q2 D.q0) = refl
normFlipX (k4 D.q3 D.q2 D.q1) = refl
normFlipX (k4 D.q3 D.q2 D.q2) = refl
normFlipX (k4 D.q3 D.q2 D.q3) = refl
normFlipX (k4 D.q3 D.q3 D.q0) = refl
normFlipX (k4 D.q3 D.q3 D.q1) = refl
normFlipX (k4 D.q3 D.q3 D.q2) = refl
normFlipX (k4 D.q3 D.q3 D.q3) = refl
normFlipY (k4 D.q0 D.q0 D.q0) = refl
normFlipY (k4 D.q0 D.q0 D.q1) = refl
normFlipY (k4 D.q0 D.q0 D.q2) = refl
normFlipY (k4 D.q0 D.q0 D.q3) = refl
normFlipY (k4 D.q0 D.q1 D.q0) = refl
normFlipY (k4 D.q0 D.q1 D.q1) = refl
normFlipY (k4 D.q0 D.q1 D.q2) = refl
normFlipY (k4 D.q0 D.q1 D.q3) = refl
normFlipY (k4 D.q0 D.q2 D.q0) = refl
normFlipY (k4 D.q0 D.q2 D.q1) = refl
normFlipY (k4 D.q0 D.q2 D.q2) = refl
normFlipY (k4 D.q0 D.q2 D.q3) = refl
normFlipY (k4 D.q0 D.q3 D.q0) = refl
normFlipY (k4 D.q0 D.q3 D.q1) = refl
normFlipY (k4 D.q0 D.q3 D.q2) = refl
normFlipY (k4 D.q0 D.q3 D.q3) = refl
normFlipY (k4 D.q1 D.q0 D.q0) = refl
normFlipY (k4 D.q1 D.q0 D.q1) = refl
normFlipY (k4 D.q1 D.q0 D.q2) = refl
normFlipY (k4 D.q1 D.q0 D.q3) = refl
normFlipY (k4 D.q1 D.q1 D.q0) = refl
normFlipY (k4 D.q1 D.q1 D.q1) = refl
normFlipY (k4 D.q1 D.q1 D.q2) = refl
normFlipY (k4 D.q1 D.q1 D.q3) = refl
normFlipY (k4 D.q1 D.q2 D.q0) = refl
normFlipY (k4 D.q1 D.q2 D.q1) = refl
normFlipY (k4 D.q1 D.q2 D.q2) = refl
normFlipY (k4 D.q1 D.q2 D.q3) = refl
normFlipY (k4 D.q1 D.q3 D.q0) = refl
normFlipY (k4 D.q1 D.q3 D.q1) = refl
normFlipY (k4 D.q1 D.q3 D.q2) = refl
normFlipY (k4 D.q1 D.q3 D.q3) = refl
normFlipY (k4 D.q2 D.q0 D.q0) = refl
normFlipY (k4 D.q2 D.q0 D.q1) = refl
normFlipY (k4 D.q2 D.q0 D.q2) = refl
normFlipY (k4 D.q2 D.q0 D.q3) = refl
normFlipY (k4 D.q2 D.q1 D.q0) = refl
normFlipY (k4 D.q2 D.q1 D.q1) = refl
normFlipY (k4 D.q2 D.q1 D.q2) = refl
normFlipY (k4 D.q2 D.q1 D.q3) = refl
normFlipY (k4 D.q2 D.q2 D.q0) = refl
normFlipY (k4 D.q2 D.q2 D.q1) = refl
normFlipY (k4 D.q2 D.q2 D.q2) = refl
normFlipY (k4 D.q2 D.q2 D.q3) = refl
normFlipY (k4 D.q2 D.q3 D.q0) = refl
normFlipY (k4 D.q2 D.q3 D.q1) = refl
normFlipY (k4 D.q2 D.q3 D.q2) = refl
normFlipY (k4 D.q2 D.q3 D.q3) = refl
normFlipY (k4 D.q3 D.q0 D.q0) = refl
normFlipY (k4 D.q3 D.q0 D.q1) = refl
normFlipY (k4 D.q3 D.q0 D.q2) = refl
normFlipY (k4 D.q3 D.q0 D.q3) = refl
normFlipY (k4 D.q3 D.q1 D.q0) = refl
normFlipY (k4 D.q3 D.q1 D.q1) = refl
normFlipY (k4 D.q3 D.q1 D.q2) = refl
normFlipY (k4 D.q3 D.q1 D.q3) = refl
normFlipY (k4 D.q3 D.q2 D.q0) = refl
normFlipY (k4 D.q3 D.q2 D.q1) = refl
normFlipY (k4 D.q3 D.q2 D.q2) = refl
normFlipY (k4 D.q3 D.q2 D.q3) = refl
normFlipY (k4 D.q3 D.q3 D.q0) = refl
normFlipY (k4 D.q3 D.q3 D.q1) = refl
normFlipY (k4 D.q3 D.q3 D.q2) = refl
normFlipY (k4 D.q3 D.q3 D.q3) = refl
normFlipZ (k4 D.q0 D.q0 D.q0) = refl
normFlipZ (k4 D.q0 D.q0 D.q1) = refl
normFlipZ (k4 D.q0 D.q0 D.q2) = refl
normFlipZ (k4 D.q0 D.q0 D.q3) = refl
normFlipZ (k4 D.q0 D.q1 D.q0) = refl
normFlipZ (k4 D.q0 D.q1 D.q1) = refl
normFlipZ (k4 D.q0 D.q1 D.q2) = refl
normFlipZ (k4 D.q0 D.q1 D.q3) = refl
normFlipZ (k4 D.q0 D.q2 D.q0) = refl
normFlipZ (k4 D.q0 D.q2 D.q1) = refl
normFlipZ (k4 D.q0 D.q2 D.q2) = refl
normFlipZ (k4 D.q0 D.q2 D.q3) = refl
normFlipZ (k4 D.q0 D.q3 D.q0) = refl
normFlipZ (k4 D.q0 D.q3 D.q1) = refl
normFlipZ (k4 D.q0 D.q3 D.q2) = refl
normFlipZ (k4 D.q0 D.q3 D.q3) = refl
normFlipZ (k4 D.q1 D.q0 D.q0) = refl
normFlipZ (k4 D.q1 D.q0 D.q1) = refl
normFlipZ (k4 D.q1 D.q0 D.q2) = refl
normFlipZ (k4 D.q1 D.q0 D.q3) = refl
normFlipZ (k4 D.q1 D.q1 D.q0) = refl
normFlipZ (k4 D.q1 D.q1 D.q1) = refl
normFlipZ (k4 D.q1 D.q1 D.q2) = refl
normFlipZ (k4 D.q1 D.q1 D.q3) = refl
normFlipZ (k4 D.q1 D.q2 D.q0) = refl
normFlipZ (k4 D.q1 D.q2 D.q1) = refl
normFlipZ (k4 D.q1 D.q2 D.q2) = refl
normFlipZ (k4 D.q1 D.q2 D.q3) = refl
normFlipZ (k4 D.q1 D.q3 D.q0) = refl
normFlipZ (k4 D.q1 D.q3 D.q1) = refl
normFlipZ (k4 D.q1 D.q3 D.q2) = refl
normFlipZ (k4 D.q1 D.q3 D.q3) = refl
normFlipZ (k4 D.q2 D.q0 D.q0) = refl
normFlipZ (k4 D.q2 D.q0 D.q1) = refl
normFlipZ (k4 D.q2 D.q0 D.q2) = refl
normFlipZ (k4 D.q2 D.q0 D.q3) = refl
normFlipZ (k4 D.q2 D.q1 D.q0) = refl
normFlipZ (k4 D.q2 D.q1 D.q1) = refl
normFlipZ (k4 D.q2 D.q1 D.q2) = refl
normFlipZ (k4 D.q2 D.q1 D.q3) = refl
normFlipZ (k4 D.q2 D.q2 D.q0) = refl
normFlipZ (k4 D.q2 D.q2 D.q1) = refl
normFlipZ (k4 D.q2 D.q2 D.q2) = refl
normFlipZ (k4 D.q2 D.q2 D.q3) = refl
normFlipZ (k4 D.q2 D.q3 D.q0) = refl
normFlipZ (k4 D.q2 D.q3 D.q1) = refl
normFlipZ (k4 D.q2 D.q3 D.q2) = refl
normFlipZ (k4 D.q2 D.q3 D.q3) = refl
normFlipZ (k4 D.q3 D.q0 D.q0) = refl
normFlipZ (k4 D.q3 D.q0 D.q1) = refl
normFlipZ (k4 D.q3 D.q0 D.q2) = refl
normFlipZ (k4 D.q3 D.q0 D.q3) = refl
normFlipZ (k4 D.q3 D.q1 D.q0) = refl
normFlipZ (k4 D.q3 D.q1 D.q1) = refl
normFlipZ (k4 D.q3 D.q1 D.q2) = refl
normFlipZ (k4 D.q3 D.q1 D.q3) = refl
normFlipZ (k4 D.q3 D.q2 D.q0) = refl
normFlipZ (k4 D.q3 D.q2 D.q1) = refl
normFlipZ (k4 D.q3 D.q2 D.q2) = refl
normFlipZ (k4 D.q3 D.q2 D.q3) = refl
normFlipZ (k4 D.q3 D.q3 D.q0) = refl
normFlipZ (k4 D.q3 D.q3 D.q1) = refl
normFlipZ (k4 D.q3 D.q3 D.q2) = refl
normFlipZ (k4 D.q3 D.q3 D.q3) = refl

-- Six permutations generated by XY/YZ adjacent transpositions.
data Perm3 : Set where
  p123 p213 p132 p312 p231 p321 : Perm3

permute : Perm3 → K4 → K4
permute p123 q = q
permute p213 q = swapXY q
permute p132 q = swapYZ q
permute p312 q = swapXY (swapYZ q)
permute p231 q = swapYZ (swapXY q)
permute p321 q = swapXY (swapYZ (swapXY q))

permInvariant : (p : Perm3) (q : K4) →
  squaredGap (permute p q) ≡ squaredGap q
permInvariant p123 q = refl
permInvariant p213 q = normSwapXY q
permInvariant p132 q = normSwapYZ q
permInvariant p312 q =
  trans (normSwapXY (swapYZ q)) (normSwapYZ q)
permInvariant p231 q =
  trans (normSwapYZ (swapXY q)) (normSwapXY q)
permInvariant p321 q =
  trans (normSwapXY (swapYZ (swapXY q)))
    (trans (normSwapYZ (swapXY q)) (normSwapXY q))

flipXIf flipYIf flipZIf : Bool → K4 → K4
flipXIf false q = q
flipXIf true q = flipX q
flipYIf false q = q
flipYIf true q = flipY q
flipZIf false q = q
flipZIf true q = flipZ q

signInvariantX : (b : Bool) (q : K4) →
  squaredGap (flipXIf b q) ≡ squaredGap q
signInvariantX false q = refl
signInvariantX true q = normFlipX q

signInvariantY : (b : Bool) (q : K4) →
  squaredGap (flipYIf b q) ≡ squaredGap q
signInvariantY false q = refl
signInvariantY true q = normFlipY q

signInvariantZ : (b : Bool) (q : K4) →
  squaredGap (flipZIf b q) ≡ squaredGap q
signInvariantZ false q = refl
signInvariantZ true q = normFlipZ q

signedPermute :
  Perm3 → Bool → Bool → Bool → K4 → K4
signedPermute p sx sy sz q =
  flipZIf sz (flipYIf sy (flipXIf sx (permute p q)))

-- All 6*2³=48 cubic signed-coordinate maps preserve the squared
-- offdiagonal hopping, without 3072 copied case branches.
squaredBandFullCubicInvariant :
  (p : Perm3) (sx sy sz : Bool) (q : K4) →
  squaredGap (signedPermute p sx sy sz q) ≡ squaredGap q
squaredBandFullCubicInvariant p sx sy sz q =
  trans (signInvariantZ sz (flipYIf sy (flipXIf sx (permute p q))))
    (trans (signInvariantY sy (flipXIf sx (permute p q)))
      (trans (signInvariantX sx (permute p q))
        (permInvariant p q)))

-- Exact gap discriminators on this *sampled ideal* spinless model.
-- No inference about electronic gap of real diamond or NV spin level.
gammaAtOrigin : gamma (k4 D.q0 D.q0 D.q0) ≡ Diff.gaussian (+ 4) (+ 0)
gammaAtOrigin = refl

originSquaredGap : squaredGap (k4 D.q0 D.q0 D.q0) ≡ + 16
originSquaredGap = refl

xSampleSquaredGap : squaredGap (k4 D.q1 D.q0 D.q0) ≡ + 0
xSampleSquaredGap = refl

diamond111SquaredGap : squaredGap (k4 D.q1 D.q1 D.q1) ≡ + 16
diamond111SquaredGap = refl

-- This is not the same Gamma as the conventional-cell *diffraction*
-- amplitude. Diffraction sums all eight atomic positions; the Bloch
-- offdiagonal sums the four nearest-neighbour A->B hopping vectors.
-- FourierPixel PR #1272's phase/intensity observer gap is relevant
-- only as a typed measurement analogy, not as a crystal device.
