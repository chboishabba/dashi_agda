module DASHI.Mathematics.Symmetry.DiamondBlochCubicCovarianceExact where

-- Full 48-operation signed cubic action on the *matrix*, not only
-- its squared energies: even sign parity fixes the finite Bloch
-- hopping amplitude; odd sign parity conjugates it and therefore
-- exchanges the two sublattice basis labels by sigma_x.
--
-- In contrast, PR #1262's Sz² no-go concerns a DIFFERENT spin-one
-- three-label action and is not overridden by this two-sublattice
-- spinless tight-binding representation.
--
-- Classical diamond lattice, Bloch, and two-site Hamiltonian
-- theory are original physical prior art; this is a source-written
-- exact finite covariance adapter for quarter-phase momentum codes.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
import Data.Integer.Properties as IntP
open import Relation.Binary.PropositionalEquality using (trans; cong)
import DASHI.Mathematics.Symmetry.DiamondNearestNeighbourBlochExact as B
import DASHI.Mathematics.Symmetry.DiamondEightSiteStructureFactorExact as Diff
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D

gammaPerm : (p : B.Perm3) (q : B.K4) →
  B.gamma (B.permute p q) ≡ B.gamma q
gammaPerm B.p123 q = refl
gammaPerm B.p213 q = B.gammaSwapXY q
gammaPerm B.p132 q = B.gammaSwapYZ q
gammaPerm B.p312 q =
  trans (B.gammaSwapXY (B.swapYZ q)) (B.gammaSwapYZ q)
gammaPerm B.p231 q =
  trans (B.gammaSwapYZ (B.swapXY q)) (B.gammaSwapXY q)
gammaPerm B.p321 q =
  trans (B.gammaSwapXY (B.swapYZ (B.swapXY q)))
    (trans (B.gammaSwapYZ (B.swapXY q)) (B.gammaSwapXY q))

signParity : Bool → Bool → Bool → Bool
signParity sx sy sz = D.xor sx (D.xor sy sz)

selectedGamma : Bool → Diff.Gaussian → Diff.Gaussian
selectedGamma false a = a
selectedGamma true a = B.conjugate a

signOrbit : Bool → Bool → Bool → B.K4 → B.K4
signOrbit sx sy sz q =
  B.flipZIf sz (B.flipYIf sy (B.flipXIf sx q))

-- All 2³ sign strings are checked on every one of 4³ phase
-- vectors. This proves the sign-parity character by closed
-- equality, not by assuming matrix covariance.
gammaSignParity :
  (sx sy sz : Bool) (q : B.K4) →
  B.gamma (signOrbit sx sy sz q)
  ≡ selectedGamma (signParity sx sy sz) (B.gamma q)
gammaSignParity false false false (B.k4 D.q0 D.q0 D.q0) = refl
gammaSignParity false false false (B.k4 D.q0 D.q0 D.q1) = refl
gammaSignParity false false false (B.k4 D.q0 D.q0 D.q2) = refl
gammaSignParity false false false (B.k4 D.q0 D.q0 D.q3) = refl
gammaSignParity false false false (B.k4 D.q0 D.q1 D.q0) = refl
gammaSignParity false false false (B.k4 D.q0 D.q1 D.q1) = refl
gammaSignParity false false false (B.k4 D.q0 D.q1 D.q2) = refl
gammaSignParity false false false (B.k4 D.q0 D.q1 D.q3) = refl
gammaSignParity false false false (B.k4 D.q0 D.q2 D.q0) = refl
gammaSignParity false false false (B.k4 D.q0 D.q2 D.q1) = refl
gammaSignParity false false false (B.k4 D.q0 D.q2 D.q2) = refl
gammaSignParity false false false (B.k4 D.q0 D.q2 D.q3) = refl
gammaSignParity false false false (B.k4 D.q0 D.q3 D.q0) = refl
gammaSignParity false false false (B.k4 D.q0 D.q3 D.q1) = refl
gammaSignParity false false false (B.k4 D.q0 D.q3 D.q2) = refl
gammaSignParity false false false (B.k4 D.q0 D.q3 D.q3) = refl
gammaSignParity false false false (B.k4 D.q1 D.q0 D.q0) = refl
gammaSignParity false false false (B.k4 D.q1 D.q0 D.q1) = refl
gammaSignParity false false false (B.k4 D.q1 D.q0 D.q2) = refl
gammaSignParity false false false (B.k4 D.q1 D.q0 D.q3) = refl
gammaSignParity false false false (B.k4 D.q1 D.q1 D.q0) = refl
gammaSignParity false false false (B.k4 D.q1 D.q1 D.q1) = refl
gammaSignParity false false false (B.k4 D.q1 D.q1 D.q2) = refl
gammaSignParity false false false (B.k4 D.q1 D.q1 D.q3) = refl
gammaSignParity false false false (B.k4 D.q1 D.q2 D.q0) = refl
gammaSignParity false false false (B.k4 D.q1 D.q2 D.q1) = refl
gammaSignParity false false false (B.k4 D.q1 D.q2 D.q2) = refl
gammaSignParity false false false (B.k4 D.q1 D.q2 D.q3) = refl
gammaSignParity false false false (B.k4 D.q1 D.q3 D.q0) = refl
gammaSignParity false false false (B.k4 D.q1 D.q3 D.q1) = refl
gammaSignParity false false false (B.k4 D.q1 D.q3 D.q2) = refl
gammaSignParity false false false (B.k4 D.q1 D.q3 D.q3) = refl
gammaSignParity false false false (B.k4 D.q2 D.q0 D.q0) = refl
gammaSignParity false false false (B.k4 D.q2 D.q0 D.q1) = refl
gammaSignParity false false false (B.k4 D.q2 D.q0 D.q2) = refl
gammaSignParity false false false (B.k4 D.q2 D.q0 D.q3) = refl
gammaSignParity false false false (B.k4 D.q2 D.q1 D.q0) = refl
gammaSignParity false false false (B.k4 D.q2 D.q1 D.q1) = refl
gammaSignParity false false false (B.k4 D.q2 D.q1 D.q2) = refl
gammaSignParity false false false (B.k4 D.q2 D.q1 D.q3) = refl
gammaSignParity false false false (B.k4 D.q2 D.q2 D.q0) = refl
gammaSignParity false false false (B.k4 D.q2 D.q2 D.q1) = refl
gammaSignParity false false false (B.k4 D.q2 D.q2 D.q2) = refl
gammaSignParity false false false (B.k4 D.q2 D.q2 D.q3) = refl
gammaSignParity false false false (B.k4 D.q2 D.q3 D.q0) = refl
gammaSignParity false false false (B.k4 D.q2 D.q3 D.q1) = refl
gammaSignParity false false false (B.k4 D.q2 D.q3 D.q2) = refl
gammaSignParity false false false (B.k4 D.q2 D.q3 D.q3) = refl
gammaSignParity false false false (B.k4 D.q3 D.q0 D.q0) = refl
gammaSignParity false false false (B.k4 D.q3 D.q0 D.q1) = refl
gammaSignParity false false false (B.k4 D.q3 D.q0 D.q2) = refl
gammaSignParity false false false (B.k4 D.q3 D.q0 D.q3) = refl
gammaSignParity false false false (B.k4 D.q3 D.q1 D.q0) = refl
gammaSignParity false false false (B.k4 D.q3 D.q1 D.q1) = refl
gammaSignParity false false false (B.k4 D.q3 D.q1 D.q2) = refl
gammaSignParity false false false (B.k4 D.q3 D.q1 D.q3) = refl
gammaSignParity false false false (B.k4 D.q3 D.q2 D.q0) = refl
gammaSignParity false false false (B.k4 D.q3 D.q2 D.q1) = refl
gammaSignParity false false false (B.k4 D.q3 D.q2 D.q2) = refl
gammaSignParity false false false (B.k4 D.q3 D.q2 D.q3) = refl
gammaSignParity false false false (B.k4 D.q3 D.q3 D.q0) = refl
gammaSignParity false false false (B.k4 D.q3 D.q3 D.q1) = refl
gammaSignParity false false false (B.k4 D.q3 D.q3 D.q2) = refl
gammaSignParity false false false (B.k4 D.q3 D.q3 D.q3) = refl
gammaSignParity false false true (B.k4 D.q0 D.q0 D.q0) = refl
gammaSignParity false false true (B.k4 D.q0 D.q0 D.q1) = refl
gammaSignParity false false true (B.k4 D.q0 D.q0 D.q2) = refl
gammaSignParity false false true (B.k4 D.q0 D.q0 D.q3) = refl
gammaSignParity false false true (B.k4 D.q0 D.q1 D.q0) = refl
gammaSignParity false false true (B.k4 D.q0 D.q1 D.q1) = refl
gammaSignParity false false true (B.k4 D.q0 D.q1 D.q2) = refl
gammaSignParity false false true (B.k4 D.q0 D.q1 D.q3) = refl
gammaSignParity false false true (B.k4 D.q0 D.q2 D.q0) = refl
gammaSignParity false false true (B.k4 D.q0 D.q2 D.q1) = refl
gammaSignParity false false true (B.k4 D.q0 D.q2 D.q2) = refl
gammaSignParity false false true (B.k4 D.q0 D.q2 D.q3) = refl
gammaSignParity false false true (B.k4 D.q0 D.q3 D.q0) = refl
gammaSignParity false false true (B.k4 D.q0 D.q3 D.q1) = refl
gammaSignParity false false true (B.k4 D.q0 D.q3 D.q2) = refl
gammaSignParity false false true (B.k4 D.q0 D.q3 D.q3) = refl
gammaSignParity false false true (B.k4 D.q1 D.q0 D.q0) = refl
gammaSignParity false false true (B.k4 D.q1 D.q0 D.q1) = refl
gammaSignParity false false true (B.k4 D.q1 D.q0 D.q2) = refl
gammaSignParity false false true (B.k4 D.q1 D.q0 D.q3) = refl
gammaSignParity false false true (B.k4 D.q1 D.q1 D.q0) = refl
gammaSignParity false false true (B.k4 D.q1 D.q1 D.q1) = refl
gammaSignParity false false true (B.k4 D.q1 D.q1 D.q2) = refl
gammaSignParity false false true (B.k4 D.q1 D.q1 D.q3) = refl
gammaSignParity false false true (B.k4 D.q1 D.q2 D.q0) = refl
gammaSignParity false false true (B.k4 D.q1 D.q2 D.q1) = refl
gammaSignParity false false true (B.k4 D.q1 D.q2 D.q2) = refl
gammaSignParity false false true (B.k4 D.q1 D.q2 D.q3) = refl
gammaSignParity false false true (B.k4 D.q1 D.q3 D.q0) = refl
gammaSignParity false false true (B.k4 D.q1 D.q3 D.q1) = refl
gammaSignParity false false true (B.k4 D.q1 D.q3 D.q2) = refl
gammaSignParity false false true (B.k4 D.q1 D.q3 D.q3) = refl
gammaSignParity false false true (B.k4 D.q2 D.q0 D.q0) = refl
gammaSignParity false false true (B.k4 D.q2 D.q0 D.q1) = refl
gammaSignParity false false true (B.k4 D.q2 D.q0 D.q2) = refl
gammaSignParity false false true (B.k4 D.q2 D.q0 D.q3) = refl
gammaSignParity false false true (B.k4 D.q2 D.q1 D.q0) = refl
gammaSignParity false false true (B.k4 D.q2 D.q1 D.q1) = refl
gammaSignParity false false true (B.k4 D.q2 D.q1 D.q2) = refl
gammaSignParity false false true (B.k4 D.q2 D.q1 D.q3) = refl
gammaSignParity false false true (B.k4 D.q2 D.q2 D.q0) = refl
gammaSignParity false false true (B.k4 D.q2 D.q2 D.q1) = refl
gammaSignParity false false true (B.k4 D.q2 D.q2 D.q2) = refl
gammaSignParity false false true (B.k4 D.q2 D.q2 D.q3) = refl
gammaSignParity false false true (B.k4 D.q2 D.q3 D.q0) = refl
gammaSignParity false false true (B.k4 D.q2 D.q3 D.q1) = refl
gammaSignParity false false true (B.k4 D.q2 D.q3 D.q2) = refl
gammaSignParity false false true (B.k4 D.q2 D.q3 D.q3) = refl
gammaSignParity false false true (B.k4 D.q3 D.q0 D.q0) = refl
gammaSignParity false false true (B.k4 D.q3 D.q0 D.q1) = refl
gammaSignParity false false true (B.k4 D.q3 D.q0 D.q2) = refl
gammaSignParity false false true (B.k4 D.q3 D.q0 D.q3) = refl
gammaSignParity false false true (B.k4 D.q3 D.q1 D.q0) = refl
gammaSignParity false false true (B.k4 D.q3 D.q1 D.q1) = refl
gammaSignParity false false true (B.k4 D.q3 D.q1 D.q2) = refl
gammaSignParity false false true (B.k4 D.q3 D.q1 D.q3) = refl
gammaSignParity false false true (B.k4 D.q3 D.q2 D.q0) = refl
gammaSignParity false false true (B.k4 D.q3 D.q2 D.q1) = refl
gammaSignParity false false true (B.k4 D.q3 D.q2 D.q2) = refl
gammaSignParity false false true (B.k4 D.q3 D.q2 D.q3) = refl
gammaSignParity false false true (B.k4 D.q3 D.q3 D.q0) = refl
gammaSignParity false false true (B.k4 D.q3 D.q3 D.q1) = refl
gammaSignParity false false true (B.k4 D.q3 D.q3 D.q2) = refl
gammaSignParity false false true (B.k4 D.q3 D.q3 D.q3) = refl
gammaSignParity false true false (B.k4 D.q0 D.q0 D.q0) = refl
gammaSignParity false true false (B.k4 D.q0 D.q0 D.q1) = refl
gammaSignParity false true false (B.k4 D.q0 D.q0 D.q2) = refl
gammaSignParity false true false (B.k4 D.q0 D.q0 D.q3) = refl
gammaSignParity false true false (B.k4 D.q0 D.q1 D.q0) = refl
gammaSignParity false true false (B.k4 D.q0 D.q1 D.q1) = refl
gammaSignParity false true false (B.k4 D.q0 D.q1 D.q2) = refl
gammaSignParity false true false (B.k4 D.q0 D.q1 D.q3) = refl
gammaSignParity false true false (B.k4 D.q0 D.q2 D.q0) = refl
gammaSignParity false true false (B.k4 D.q0 D.q2 D.q1) = refl
gammaSignParity false true false (B.k4 D.q0 D.q2 D.q2) = refl
gammaSignParity false true false (B.k4 D.q0 D.q2 D.q3) = refl
gammaSignParity false true false (B.k4 D.q0 D.q3 D.q0) = refl
gammaSignParity false true false (B.k4 D.q0 D.q3 D.q1) = refl
gammaSignParity false true false (B.k4 D.q0 D.q3 D.q2) = refl
gammaSignParity false true false (B.k4 D.q0 D.q3 D.q3) = refl
gammaSignParity false true false (B.k4 D.q1 D.q0 D.q0) = refl
gammaSignParity false true false (B.k4 D.q1 D.q0 D.q1) = refl
gammaSignParity false true false (B.k4 D.q1 D.q0 D.q2) = refl
gammaSignParity false true false (B.k4 D.q1 D.q0 D.q3) = refl
gammaSignParity false true false (B.k4 D.q1 D.q1 D.q0) = refl
gammaSignParity false true false (B.k4 D.q1 D.q1 D.q1) = refl
gammaSignParity false true false (B.k4 D.q1 D.q1 D.q2) = refl
gammaSignParity false true false (B.k4 D.q1 D.q1 D.q3) = refl
gammaSignParity false true false (B.k4 D.q1 D.q2 D.q0) = refl
gammaSignParity false true false (B.k4 D.q1 D.q2 D.q1) = refl
gammaSignParity false true false (B.k4 D.q1 D.q2 D.q2) = refl
gammaSignParity false true false (B.k4 D.q1 D.q2 D.q3) = refl
gammaSignParity false true false (B.k4 D.q1 D.q3 D.q0) = refl
gammaSignParity false true false (B.k4 D.q1 D.q3 D.q1) = refl
gammaSignParity false true false (B.k4 D.q1 D.q3 D.q2) = refl
gammaSignParity false true false (B.k4 D.q1 D.q3 D.q3) = refl
gammaSignParity false true false (B.k4 D.q2 D.q0 D.q0) = refl
gammaSignParity false true false (B.k4 D.q2 D.q0 D.q1) = refl
gammaSignParity false true false (B.k4 D.q2 D.q0 D.q2) = refl
gammaSignParity false true false (B.k4 D.q2 D.q0 D.q3) = refl
gammaSignParity false true false (B.k4 D.q2 D.q1 D.q0) = refl
gammaSignParity false true false (B.k4 D.q2 D.q1 D.q1) = refl
gammaSignParity false true false (B.k4 D.q2 D.q1 D.q2) = refl
gammaSignParity false true false (B.k4 D.q2 D.q1 D.q3) = refl
gammaSignParity false true false (B.k4 D.q2 D.q2 D.q0) = refl
gammaSignParity false true false (B.k4 D.q2 D.q2 D.q1) = refl
gammaSignParity false true false (B.k4 D.q2 D.q2 D.q2) = refl
gammaSignParity false true false (B.k4 D.q2 D.q2 D.q3) = refl
gammaSignParity false true false (B.k4 D.q2 D.q3 D.q0) = refl
gammaSignParity false true false (B.k4 D.q2 D.q3 D.q1) = refl
gammaSignParity false true false (B.k4 D.q2 D.q3 D.q2) = refl
gammaSignParity false true false (B.k4 D.q2 D.q3 D.q3) = refl
gammaSignParity false true false (B.k4 D.q3 D.q0 D.q0) = refl
gammaSignParity false true false (B.k4 D.q3 D.q0 D.q1) = refl
gammaSignParity false true false (B.k4 D.q3 D.q0 D.q2) = refl
gammaSignParity false true false (B.k4 D.q3 D.q0 D.q3) = refl
gammaSignParity false true false (B.k4 D.q3 D.q1 D.q0) = refl
gammaSignParity false true false (B.k4 D.q3 D.q1 D.q1) = refl
gammaSignParity false true false (B.k4 D.q3 D.q1 D.q2) = refl
gammaSignParity false true false (B.k4 D.q3 D.q1 D.q3) = refl
gammaSignParity false true false (B.k4 D.q3 D.q2 D.q0) = refl
gammaSignParity false true false (B.k4 D.q3 D.q2 D.q1) = refl
gammaSignParity false true false (B.k4 D.q3 D.q2 D.q2) = refl
gammaSignParity false true false (B.k4 D.q3 D.q2 D.q3) = refl
gammaSignParity false true false (B.k4 D.q3 D.q3 D.q0) = refl
gammaSignParity false true false (B.k4 D.q3 D.q3 D.q1) = refl
gammaSignParity false true false (B.k4 D.q3 D.q3 D.q2) = refl
gammaSignParity false true false (B.k4 D.q3 D.q3 D.q3) = refl
gammaSignParity false true true (B.k4 D.q0 D.q0 D.q0) = refl
gammaSignParity false true true (B.k4 D.q0 D.q0 D.q1) = refl
gammaSignParity false true true (B.k4 D.q0 D.q0 D.q2) = refl
gammaSignParity false true true (B.k4 D.q0 D.q0 D.q3) = refl
gammaSignParity false true true (B.k4 D.q0 D.q1 D.q0) = refl
gammaSignParity false true true (B.k4 D.q0 D.q1 D.q1) = refl
gammaSignParity false true true (B.k4 D.q0 D.q1 D.q2) = refl
gammaSignParity false true true (B.k4 D.q0 D.q1 D.q3) = refl
gammaSignParity false true true (B.k4 D.q0 D.q2 D.q0) = refl
gammaSignParity false true true (B.k4 D.q0 D.q2 D.q1) = refl
gammaSignParity false true true (B.k4 D.q0 D.q2 D.q2) = refl
gammaSignParity false true true (B.k4 D.q0 D.q2 D.q3) = refl
gammaSignParity false true true (B.k4 D.q0 D.q3 D.q0) = refl
gammaSignParity false true true (B.k4 D.q0 D.q3 D.q1) = refl
gammaSignParity false true true (B.k4 D.q0 D.q3 D.q2) = refl
gammaSignParity false true true (B.k4 D.q0 D.q3 D.q3) = refl
gammaSignParity false true true (B.k4 D.q1 D.q0 D.q0) = refl
gammaSignParity false true true (B.k4 D.q1 D.q0 D.q1) = refl
gammaSignParity false true true (B.k4 D.q1 D.q0 D.q2) = refl
gammaSignParity false true true (B.k4 D.q1 D.q0 D.q3) = refl
gammaSignParity false true true (B.k4 D.q1 D.q1 D.q0) = refl
gammaSignParity false true true (B.k4 D.q1 D.q1 D.q1) = refl
gammaSignParity false true true (B.k4 D.q1 D.q1 D.q2) = refl
gammaSignParity false true true (B.k4 D.q1 D.q1 D.q3) = refl
gammaSignParity false true true (B.k4 D.q1 D.q2 D.q0) = refl
gammaSignParity false true true (B.k4 D.q1 D.q2 D.q1) = refl
gammaSignParity false true true (B.k4 D.q1 D.q2 D.q2) = refl
gammaSignParity false true true (B.k4 D.q1 D.q2 D.q3) = refl
gammaSignParity false true true (B.k4 D.q1 D.q3 D.q0) = refl
gammaSignParity false true true (B.k4 D.q1 D.q3 D.q1) = refl
gammaSignParity false true true (B.k4 D.q1 D.q3 D.q2) = refl
gammaSignParity false true true (B.k4 D.q1 D.q3 D.q3) = refl
gammaSignParity false true true (B.k4 D.q2 D.q0 D.q0) = refl
gammaSignParity false true true (B.k4 D.q2 D.q0 D.q1) = refl
gammaSignParity false true true (B.k4 D.q2 D.q0 D.q2) = refl
gammaSignParity false true true (B.k4 D.q2 D.q0 D.q3) = refl
gammaSignParity false true true (B.k4 D.q2 D.q1 D.q0) = refl
gammaSignParity false true true (B.k4 D.q2 D.q1 D.q1) = refl
gammaSignParity false true true (B.k4 D.q2 D.q1 D.q2) = refl
gammaSignParity false true true (B.k4 D.q2 D.q1 D.q3) = refl
gammaSignParity false true true (B.k4 D.q2 D.q2 D.q0) = refl
gammaSignParity false true true (B.k4 D.q2 D.q2 D.q1) = refl
gammaSignParity false true true (B.k4 D.q2 D.q2 D.q2) = refl
gammaSignParity false true true (B.k4 D.q2 D.q2 D.q3) = refl
gammaSignParity false true true (B.k4 D.q2 D.q3 D.q0) = refl
gammaSignParity false true true (B.k4 D.q2 D.q3 D.q1) = refl
gammaSignParity false true true (B.k4 D.q2 D.q3 D.q2) = refl
gammaSignParity false true true (B.k4 D.q2 D.q3 D.q3) = refl
gammaSignParity false true true (B.k4 D.q3 D.q0 D.q0) = refl
gammaSignParity false true true (B.k4 D.q3 D.q0 D.q1) = refl
gammaSignParity false true true (B.k4 D.q3 D.q0 D.q2) = refl
gammaSignParity false true true (B.k4 D.q3 D.q0 D.q3) = refl
gammaSignParity false true true (B.k4 D.q3 D.q1 D.q0) = refl
gammaSignParity false true true (B.k4 D.q3 D.q1 D.q1) = refl
gammaSignParity false true true (B.k4 D.q3 D.q1 D.q2) = refl
gammaSignParity false true true (B.k4 D.q3 D.q1 D.q3) = refl
gammaSignParity false true true (B.k4 D.q3 D.q2 D.q0) = refl
gammaSignParity false true true (B.k4 D.q3 D.q2 D.q1) = refl
gammaSignParity false true true (B.k4 D.q3 D.q2 D.q2) = refl
gammaSignParity false true true (B.k4 D.q3 D.q2 D.q3) = refl
gammaSignParity false true true (B.k4 D.q3 D.q3 D.q0) = refl
gammaSignParity false true true (B.k4 D.q3 D.q3 D.q1) = refl
gammaSignParity false true true (B.k4 D.q3 D.q3 D.q2) = refl
gammaSignParity false true true (B.k4 D.q3 D.q3 D.q3) = refl
gammaSignParity true false false (B.k4 D.q0 D.q0 D.q0) = refl
gammaSignParity true false false (B.k4 D.q0 D.q0 D.q1) = refl
gammaSignParity true false false (B.k4 D.q0 D.q0 D.q2) = refl
gammaSignParity true false false (B.k4 D.q0 D.q0 D.q3) = refl
gammaSignParity true false false (B.k4 D.q0 D.q1 D.q0) = refl
gammaSignParity true false false (B.k4 D.q0 D.q1 D.q1) = refl
gammaSignParity true false false (B.k4 D.q0 D.q1 D.q2) = refl
gammaSignParity true false false (B.k4 D.q0 D.q1 D.q3) = refl
gammaSignParity true false false (B.k4 D.q0 D.q2 D.q0) = refl
gammaSignParity true false false (B.k4 D.q0 D.q2 D.q1) = refl
gammaSignParity true false false (B.k4 D.q0 D.q2 D.q2) = refl
gammaSignParity true false false (B.k4 D.q0 D.q2 D.q3) = refl
gammaSignParity true false false (B.k4 D.q0 D.q3 D.q0) = refl
gammaSignParity true false false (B.k4 D.q0 D.q3 D.q1) = refl
gammaSignParity true false false (B.k4 D.q0 D.q3 D.q2) = refl
gammaSignParity true false false (B.k4 D.q0 D.q3 D.q3) = refl
gammaSignParity true false false (B.k4 D.q1 D.q0 D.q0) = refl
gammaSignParity true false false (B.k4 D.q1 D.q0 D.q1) = refl
gammaSignParity true false false (B.k4 D.q1 D.q0 D.q2) = refl
gammaSignParity true false false (B.k4 D.q1 D.q0 D.q3) = refl
gammaSignParity true false false (B.k4 D.q1 D.q1 D.q0) = refl
gammaSignParity true false false (B.k4 D.q1 D.q1 D.q1) = refl
gammaSignParity true false false (B.k4 D.q1 D.q1 D.q2) = refl
gammaSignParity true false false (B.k4 D.q1 D.q1 D.q3) = refl
gammaSignParity true false false (B.k4 D.q1 D.q2 D.q0) = refl
gammaSignParity true false false (B.k4 D.q1 D.q2 D.q1) = refl
gammaSignParity true false false (B.k4 D.q1 D.q2 D.q2) = refl
gammaSignParity true false false (B.k4 D.q1 D.q2 D.q3) = refl
gammaSignParity true false false (B.k4 D.q1 D.q3 D.q0) = refl
gammaSignParity true false false (B.k4 D.q1 D.q3 D.q1) = refl
gammaSignParity true false false (B.k4 D.q1 D.q3 D.q2) = refl
gammaSignParity true false false (B.k4 D.q1 D.q3 D.q3) = refl
gammaSignParity true false false (B.k4 D.q2 D.q0 D.q0) = refl
gammaSignParity true false false (B.k4 D.q2 D.q0 D.q1) = refl
gammaSignParity true false false (B.k4 D.q2 D.q0 D.q2) = refl
gammaSignParity true false false (B.k4 D.q2 D.q0 D.q3) = refl
gammaSignParity true false false (B.k4 D.q2 D.q1 D.q0) = refl
gammaSignParity true false false (B.k4 D.q2 D.q1 D.q1) = refl
gammaSignParity true false false (B.k4 D.q2 D.q1 D.q2) = refl
gammaSignParity true false false (B.k4 D.q2 D.q1 D.q3) = refl
gammaSignParity true false false (B.k4 D.q2 D.q2 D.q0) = refl
gammaSignParity true false false (B.k4 D.q2 D.q2 D.q1) = refl
gammaSignParity true false false (B.k4 D.q2 D.q2 D.q2) = refl
gammaSignParity true false false (B.k4 D.q2 D.q2 D.q3) = refl
gammaSignParity true false false (B.k4 D.q2 D.q3 D.q0) = refl
gammaSignParity true false false (B.k4 D.q2 D.q3 D.q1) = refl
gammaSignParity true false false (B.k4 D.q2 D.q3 D.q2) = refl
gammaSignParity true false false (B.k4 D.q2 D.q3 D.q3) = refl
gammaSignParity true false false (B.k4 D.q3 D.q0 D.q0) = refl
gammaSignParity true false false (B.k4 D.q3 D.q0 D.q1) = refl
gammaSignParity true false false (B.k4 D.q3 D.q0 D.q2) = refl
gammaSignParity true false false (B.k4 D.q3 D.q0 D.q3) = refl
gammaSignParity true false false (B.k4 D.q3 D.q1 D.q0) = refl
gammaSignParity true false false (B.k4 D.q3 D.q1 D.q1) = refl
gammaSignParity true false false (B.k4 D.q3 D.q1 D.q2) = refl
gammaSignParity true false false (B.k4 D.q3 D.q1 D.q3) = refl
gammaSignParity true false false (B.k4 D.q3 D.q2 D.q0) = refl
gammaSignParity true false false (B.k4 D.q3 D.q2 D.q1) = refl
gammaSignParity true false false (B.k4 D.q3 D.q2 D.q2) = refl
gammaSignParity true false false (B.k4 D.q3 D.q2 D.q3) = refl
gammaSignParity true false false (B.k4 D.q3 D.q3 D.q0) = refl
gammaSignParity true false false (B.k4 D.q3 D.q3 D.q1) = refl
gammaSignParity true false false (B.k4 D.q3 D.q3 D.q2) = refl
gammaSignParity true false false (B.k4 D.q3 D.q3 D.q3) = refl
gammaSignParity true false true (B.k4 D.q0 D.q0 D.q0) = refl
gammaSignParity true false true (B.k4 D.q0 D.q0 D.q1) = refl
gammaSignParity true false true (B.k4 D.q0 D.q0 D.q2) = refl
gammaSignParity true false true (B.k4 D.q0 D.q0 D.q3) = refl
gammaSignParity true false true (B.k4 D.q0 D.q1 D.q0) = refl
gammaSignParity true false true (B.k4 D.q0 D.q1 D.q1) = refl
gammaSignParity true false true (B.k4 D.q0 D.q1 D.q2) = refl
gammaSignParity true false true (B.k4 D.q0 D.q1 D.q3) = refl
gammaSignParity true false true (B.k4 D.q0 D.q2 D.q0) = refl
gammaSignParity true false true (B.k4 D.q0 D.q2 D.q1) = refl
gammaSignParity true false true (B.k4 D.q0 D.q2 D.q2) = refl
gammaSignParity true false true (B.k4 D.q0 D.q2 D.q3) = refl
gammaSignParity true false true (B.k4 D.q0 D.q3 D.q0) = refl
gammaSignParity true false true (B.k4 D.q0 D.q3 D.q1) = refl
gammaSignParity true false true (B.k4 D.q0 D.q3 D.q2) = refl
gammaSignParity true false true (B.k4 D.q0 D.q3 D.q3) = refl
gammaSignParity true false true (B.k4 D.q1 D.q0 D.q0) = refl
gammaSignParity true false true (B.k4 D.q1 D.q0 D.q1) = refl
gammaSignParity true false true (B.k4 D.q1 D.q0 D.q2) = refl
gammaSignParity true false true (B.k4 D.q1 D.q0 D.q3) = refl
gammaSignParity true false true (B.k4 D.q1 D.q1 D.q0) = refl
gammaSignParity true false true (B.k4 D.q1 D.q1 D.q1) = refl
gammaSignParity true false true (B.k4 D.q1 D.q1 D.q2) = refl
gammaSignParity true false true (B.k4 D.q1 D.q1 D.q3) = refl
gammaSignParity true false true (B.k4 D.q1 D.q2 D.q0) = refl
gammaSignParity true false true (B.k4 D.q1 D.q2 D.q1) = refl
gammaSignParity true false true (B.k4 D.q1 D.q2 D.q2) = refl
gammaSignParity true false true (B.k4 D.q1 D.q2 D.q3) = refl
gammaSignParity true false true (B.k4 D.q1 D.q3 D.q0) = refl
gammaSignParity true false true (B.k4 D.q1 D.q3 D.q1) = refl
gammaSignParity true false true (B.k4 D.q1 D.q3 D.q2) = refl
gammaSignParity true false true (B.k4 D.q1 D.q3 D.q3) = refl
gammaSignParity true false true (B.k4 D.q2 D.q0 D.q0) = refl
gammaSignParity true false true (B.k4 D.q2 D.q0 D.q1) = refl
gammaSignParity true false true (B.k4 D.q2 D.q0 D.q2) = refl
gammaSignParity true false true (B.k4 D.q2 D.q0 D.q3) = refl
gammaSignParity true false true (B.k4 D.q2 D.q1 D.q0) = refl
gammaSignParity true false true (B.k4 D.q2 D.q1 D.q1) = refl
gammaSignParity true false true (B.k4 D.q2 D.q1 D.q2) = refl
gammaSignParity true false true (B.k4 D.q2 D.q1 D.q3) = refl
gammaSignParity true false true (B.k4 D.q2 D.q2 D.q0) = refl
gammaSignParity true false true (B.k4 D.q2 D.q2 D.q1) = refl
gammaSignParity true false true (B.k4 D.q2 D.q2 D.q2) = refl
gammaSignParity true false true (B.k4 D.q2 D.q2 D.q3) = refl
gammaSignParity true false true (B.k4 D.q2 D.q3 D.q0) = refl
gammaSignParity true false true (B.k4 D.q2 D.q3 D.q1) = refl
gammaSignParity true false true (B.k4 D.q2 D.q3 D.q2) = refl
gammaSignParity true false true (B.k4 D.q2 D.q3 D.q3) = refl
gammaSignParity true false true (B.k4 D.q3 D.q0 D.q0) = refl
gammaSignParity true false true (B.k4 D.q3 D.q0 D.q1) = refl
gammaSignParity true false true (B.k4 D.q3 D.q0 D.q2) = refl
gammaSignParity true false true (B.k4 D.q3 D.q0 D.q3) = refl
gammaSignParity true false true (B.k4 D.q3 D.q1 D.q0) = refl
gammaSignParity true false true (B.k4 D.q3 D.q1 D.q1) = refl
gammaSignParity true false true (B.k4 D.q3 D.q1 D.q2) = refl
gammaSignParity true false true (B.k4 D.q3 D.q1 D.q3) = refl
gammaSignParity true false true (B.k4 D.q3 D.q2 D.q0) = refl
gammaSignParity true false true (B.k4 D.q3 D.q2 D.q1) = refl
gammaSignParity true false true (B.k4 D.q3 D.q2 D.q2) = refl
gammaSignParity true false true (B.k4 D.q3 D.q2 D.q3) = refl
gammaSignParity true false true (B.k4 D.q3 D.q3 D.q0) = refl
gammaSignParity true false true (B.k4 D.q3 D.q3 D.q1) = refl
gammaSignParity true false true (B.k4 D.q3 D.q3 D.q2) = refl
gammaSignParity true false true (B.k4 D.q3 D.q3 D.q3) = refl
gammaSignParity true true false (B.k4 D.q0 D.q0 D.q0) = refl
gammaSignParity true true false (B.k4 D.q0 D.q0 D.q1) = refl
gammaSignParity true true false (B.k4 D.q0 D.q0 D.q2) = refl
gammaSignParity true true false (B.k4 D.q0 D.q0 D.q3) = refl
gammaSignParity true true false (B.k4 D.q0 D.q1 D.q0) = refl
gammaSignParity true true false (B.k4 D.q0 D.q1 D.q1) = refl
gammaSignParity true true false (B.k4 D.q0 D.q1 D.q2) = refl
gammaSignParity true true false (B.k4 D.q0 D.q1 D.q3) = refl
gammaSignParity true true false (B.k4 D.q0 D.q2 D.q0) = refl
gammaSignParity true true false (B.k4 D.q0 D.q2 D.q1) = refl
gammaSignParity true true false (B.k4 D.q0 D.q2 D.q2) = refl
gammaSignParity true true false (B.k4 D.q0 D.q2 D.q3) = refl
gammaSignParity true true false (B.k4 D.q0 D.q3 D.q0) = refl
gammaSignParity true true false (B.k4 D.q0 D.q3 D.q1) = refl
gammaSignParity true true false (B.k4 D.q0 D.q3 D.q2) = refl
gammaSignParity true true false (B.k4 D.q0 D.q3 D.q3) = refl
gammaSignParity true true false (B.k4 D.q1 D.q0 D.q0) = refl
gammaSignParity true true false (B.k4 D.q1 D.q0 D.q1) = refl
gammaSignParity true true false (B.k4 D.q1 D.q0 D.q2) = refl
gammaSignParity true true false (B.k4 D.q1 D.q0 D.q3) = refl
gammaSignParity true true false (B.k4 D.q1 D.q1 D.q0) = refl
gammaSignParity true true false (B.k4 D.q1 D.q1 D.q1) = refl
gammaSignParity true true false (B.k4 D.q1 D.q1 D.q2) = refl
gammaSignParity true true false (B.k4 D.q1 D.q1 D.q3) = refl
gammaSignParity true true false (B.k4 D.q1 D.q2 D.q0) = refl
gammaSignParity true true false (B.k4 D.q1 D.q2 D.q1) = refl
gammaSignParity true true false (B.k4 D.q1 D.q2 D.q2) = refl
gammaSignParity true true false (B.k4 D.q1 D.q2 D.q3) = refl
gammaSignParity true true false (B.k4 D.q1 D.q3 D.q0) = refl
gammaSignParity true true false (B.k4 D.q1 D.q3 D.q1) = refl
gammaSignParity true true false (B.k4 D.q1 D.q3 D.q2) = refl
gammaSignParity true true false (B.k4 D.q1 D.q3 D.q3) = refl
gammaSignParity true true false (B.k4 D.q2 D.q0 D.q0) = refl
gammaSignParity true true false (B.k4 D.q2 D.q0 D.q1) = refl
gammaSignParity true true false (B.k4 D.q2 D.q0 D.q2) = refl
gammaSignParity true true false (B.k4 D.q2 D.q0 D.q3) = refl
gammaSignParity true true false (B.k4 D.q2 D.q1 D.q0) = refl
gammaSignParity true true false (B.k4 D.q2 D.q1 D.q1) = refl
gammaSignParity true true false (B.k4 D.q2 D.q1 D.q2) = refl
gammaSignParity true true false (B.k4 D.q2 D.q1 D.q3) = refl
gammaSignParity true true false (B.k4 D.q2 D.q2 D.q0) = refl
gammaSignParity true true false (B.k4 D.q2 D.q2 D.q1) = refl
gammaSignParity true true false (B.k4 D.q2 D.q2 D.q2) = refl
gammaSignParity true true false (B.k4 D.q2 D.q2 D.q3) = refl
gammaSignParity true true false (B.k4 D.q2 D.q3 D.q0) = refl
gammaSignParity true true false (B.k4 D.q2 D.q3 D.q1) = refl
gammaSignParity true true false (B.k4 D.q2 D.q3 D.q2) = refl
gammaSignParity true true false (B.k4 D.q2 D.q3 D.q3) = refl
gammaSignParity true true false (B.k4 D.q3 D.q0 D.q0) = refl
gammaSignParity true true false (B.k4 D.q3 D.q0 D.q1) = refl
gammaSignParity true true false (B.k4 D.q3 D.q0 D.q2) = refl
gammaSignParity true true false (B.k4 D.q3 D.q0 D.q3) = refl
gammaSignParity true true false (B.k4 D.q3 D.q1 D.q0) = refl
gammaSignParity true true false (B.k4 D.q3 D.q1 D.q1) = refl
gammaSignParity true true false (B.k4 D.q3 D.q1 D.q2) = refl
gammaSignParity true true false (B.k4 D.q3 D.q1 D.q3) = refl
gammaSignParity true true false (B.k4 D.q3 D.q2 D.q0) = refl
gammaSignParity true true false (B.k4 D.q3 D.q2 D.q1) = refl
gammaSignParity true true false (B.k4 D.q3 D.q2 D.q2) = refl
gammaSignParity true true false (B.k4 D.q3 D.q2 D.q3) = refl
gammaSignParity true true false (B.k4 D.q3 D.q3 D.q0) = refl
gammaSignParity true true false (B.k4 D.q3 D.q3 D.q1) = refl
gammaSignParity true true false (B.k4 D.q3 D.q3 D.q2) = refl
gammaSignParity true true false (B.k4 D.q3 D.q3 D.q3) = refl
gammaSignParity true true true (B.k4 D.q0 D.q0 D.q0) = refl
gammaSignParity true true true (B.k4 D.q0 D.q0 D.q1) = refl
gammaSignParity true true true (B.k4 D.q0 D.q0 D.q2) = refl
gammaSignParity true true true (B.k4 D.q0 D.q0 D.q3) = refl
gammaSignParity true true true (B.k4 D.q0 D.q1 D.q0) = refl
gammaSignParity true true true (B.k4 D.q0 D.q1 D.q1) = refl
gammaSignParity true true true (B.k4 D.q0 D.q1 D.q2) = refl
gammaSignParity true true true (B.k4 D.q0 D.q1 D.q3) = refl
gammaSignParity true true true (B.k4 D.q0 D.q2 D.q0) = refl
gammaSignParity true true true (B.k4 D.q0 D.q2 D.q1) = refl
gammaSignParity true true true (B.k4 D.q0 D.q2 D.q2) = refl
gammaSignParity true true true (B.k4 D.q0 D.q2 D.q3) = refl
gammaSignParity true true true (B.k4 D.q0 D.q3 D.q0) = refl
gammaSignParity true true true (B.k4 D.q0 D.q3 D.q1) = refl
gammaSignParity true true true (B.k4 D.q0 D.q3 D.q2) = refl
gammaSignParity true true true (B.k4 D.q0 D.q3 D.q3) = refl
gammaSignParity true true true (B.k4 D.q1 D.q0 D.q0) = refl
gammaSignParity true true true (B.k4 D.q1 D.q0 D.q1) = refl
gammaSignParity true true true (B.k4 D.q1 D.q0 D.q2) = refl
gammaSignParity true true true (B.k4 D.q1 D.q0 D.q3) = refl
gammaSignParity true true true (B.k4 D.q1 D.q1 D.q0) = refl
gammaSignParity true true true (B.k4 D.q1 D.q1 D.q1) = refl
gammaSignParity true true true (B.k4 D.q1 D.q1 D.q2) = refl
gammaSignParity true true true (B.k4 D.q1 D.q1 D.q3) = refl
gammaSignParity true true true (B.k4 D.q1 D.q2 D.q0) = refl
gammaSignParity true true true (B.k4 D.q1 D.q2 D.q1) = refl
gammaSignParity true true true (B.k4 D.q1 D.q2 D.q2) = refl
gammaSignParity true true true (B.k4 D.q1 D.q2 D.q3) = refl
gammaSignParity true true true (B.k4 D.q1 D.q3 D.q0) = refl
gammaSignParity true true true (B.k4 D.q1 D.q3 D.q1) = refl
gammaSignParity true true true (B.k4 D.q1 D.q3 D.q2) = refl
gammaSignParity true true true (B.k4 D.q1 D.q3 D.q3) = refl
gammaSignParity true true true (B.k4 D.q2 D.q0 D.q0) = refl
gammaSignParity true true true (B.k4 D.q2 D.q0 D.q1) = refl
gammaSignParity true true true (B.k4 D.q2 D.q0 D.q2) = refl
gammaSignParity true true true (B.k4 D.q2 D.q0 D.q3) = refl
gammaSignParity true true true (B.k4 D.q2 D.q1 D.q0) = refl
gammaSignParity true true true (B.k4 D.q2 D.q1 D.q1) = refl
gammaSignParity true true true (B.k4 D.q2 D.q1 D.q2) = refl
gammaSignParity true true true (B.k4 D.q2 D.q1 D.q3) = refl
gammaSignParity true true true (B.k4 D.q2 D.q2 D.q0) = refl
gammaSignParity true true true (B.k4 D.q2 D.q2 D.q1) = refl
gammaSignParity true true true (B.k4 D.q2 D.q2 D.q2) = refl
gammaSignParity true true true (B.k4 D.q2 D.q2 D.q3) = refl
gammaSignParity true true true (B.k4 D.q2 D.q3 D.q0) = refl
gammaSignParity true true true (B.k4 D.q2 D.q3 D.q1) = refl
gammaSignParity true true true (B.k4 D.q2 D.q3 D.q2) = refl
gammaSignParity true true true (B.k4 D.q2 D.q3 D.q3) = refl
gammaSignParity true true true (B.k4 D.q3 D.q0 D.q0) = refl
gammaSignParity true true true (B.k4 D.q3 D.q0 D.q1) = refl
gammaSignParity true true true (B.k4 D.q3 D.q0 D.q2) = refl
gammaSignParity true true true (B.k4 D.q3 D.q0 D.q3) = refl
gammaSignParity true true true (B.k4 D.q3 D.q1 D.q0) = refl
gammaSignParity true true true (B.k4 D.q3 D.q1 D.q1) = refl
gammaSignParity true true true (B.k4 D.q3 D.q1 D.q2) = refl
gammaSignParity true true true (B.k4 D.q3 D.q1 D.q3) = refl
gammaSignParity true true true (B.k4 D.q3 D.q2 D.q0) = refl
gammaSignParity true true true (B.k4 D.q3 D.q2 D.q1) = refl
gammaSignParity true true true (B.k4 D.q3 D.q2 D.q2) = refl
gammaSignParity true true true (B.k4 D.q3 D.q2 D.q3) = refl
gammaSignParity true true true (B.k4 D.q3 D.q3 D.q0) = refl
gammaSignParity true true true (B.k4 D.q3 D.q3 D.q1) = refl
gammaSignParity true true true (B.k4 D.q3 D.q3 D.q2) = refl
gammaSignParity true true true (B.k4 D.q3 D.q3 D.q3) = refl

fullCubicGammaCovariance :
  (p : B.Perm3) (sx sy sz : Bool) (q : B.K4) →
  B.gamma (B.signedPermute p sx sy sz q) ≡
  selectedGamma (signParity sx sy sz) (B.gamma q)
fullCubicGammaCovariance p sx sy sz q =
  trans (gammaSignParity sx sy sz (B.permute p q))
        (cong (selectedGamma (signParity sx sy sz))
          (gammaPerm p q))

conjugateInvolutive : (z : Diff.Gaussian) →
  B.conjugate (B.conjugate z) ≡ z
conjugateInvolutive (Diff.gaussian a b)
  rewrite IntP.neg-involutive b = refl

-- An actual sublattice basis swap acts as sigma_x H sigma_x.
swapSublattices : B.Bloch2 → B.Bloch2
swapSublattices (B.bloch2 aa ab ba bb) =
  B.bloch2 bb ba ab aa

selectedMatrix : Bool → B.Bloch2 → B.Bloch2
selectedMatrix false H = H
selectedMatrix true H = swapSublattices H

hamiltonianFromAmplitude :
  (parity : Bool) (q r : B.K4) →
  B.gamma r ≡ selectedGamma parity (B.gamma q) →
  B.hamiltonian r ≡ selectedMatrix parity (B.hamiltonian q)
hamiltonianFromAmplitude false q r agrees
  rewrite agrees = refl
hamiltonianFromAmplitude true q r agrees
  rewrite agrees | conjugateInvolutive (B.gamma q) = refl

-- This stronger theorem tracks the represented *two-site basis*
-- while establishing 48-operation matrix covariance. It does NOT
-- assert that an A/B-contrasted NV defect Hamiltonian shares it.
fullCubicBlochCovariance :
  (p : B.Perm3) (sx sy sz : Bool) (q : B.K4) →
  B.hamiltonian (B.signedPermute p sx sy sz q)
  ≡ selectedMatrix (signParity sx sy sz) (B.hamiltonian q)
fullCubicBlochCovariance p sx sy sz q =
  hamiltonianFromAmplitude (signParity sx sy sz) q
    (B.signedPermute p sx sy sz q)
    (fullCubicGammaCovariance p sx sy sz q)

-- A general Fd-3m operation also has a *fractional translation*
-- and Bloch gauge phase. This finite B3 matrix intertwiner by itself
-- must not be promoted to a representation of all 192 Seitz cosets.
