module DASHI.Mathematics.Symmetry.DiamondFccReciprocalResidueCriterionExact where

-- Finite *bidirectional* fcc reciprocal criterion in ℤ/4.
-- Fcc primitive generators in quarter-cell coordinates are:
-- t1=(0,2,2), t2=(2,0,2), t3=(2,2,0).
-- A wavevector h,k,l gives an integral phase on each iff the
-- three residues are all even or all odd. This is the finite
-- residue complement of DiamondFccBccReciprocalExact's forward
-- arbitrary-integer winding theorem, not an unproved integer
-- division theorem. IUCr fcc reflection conditions are prior art.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D
import DASHI.Mathematics.Symmetry.DiamondEightSiteStructureFactorExact as Diff

isZeroResidue : D.Quarter → Bool
isZeroResidue D.q0 = true
isZeroResidue D.q1 = false
isZeroResidue D.q2 = false
isZeroResidue D.q3 = false

fccPairingsVanish : D.Quarter → D.Quarter → D.Quarter → Bool
fccPairingsVanish h k l =
  Diff.and
    (isZeroResidue (D.add (Diff.mul4 D.q2 k) (Diff.mul4 D.q2 l)))
    (Diff.and
      (isZeroResidue (D.add (Diff.mul4 D.q2 h) (Diff.mul4 D.q2 l)))
      (isZeroResidue (D.add (Diff.mul4 D.q2 h) (Diff.mul4 D.q2 k))))

-- This is a genuine iff encoded by equality of two computed Booleans,
-- not only an 0..3 spot check.
fccReciprocalIffSameParity :
  (h k l : D.Quarter) →
  fccPairingsVanish h k l ≡ Diff.unmixed h k l
fccReciprocalIffSameParity D.q0 D.q0 D.q0 = refl
fccReciprocalIffSameParity D.q0 D.q0 D.q1 = refl
fccReciprocalIffSameParity D.q0 D.q0 D.q2 = refl
fccReciprocalIffSameParity D.q0 D.q0 D.q3 = refl
fccReciprocalIffSameParity D.q0 D.q1 D.q0 = refl
fccReciprocalIffSameParity D.q0 D.q1 D.q1 = refl
fccReciprocalIffSameParity D.q0 D.q1 D.q2 = refl
fccReciprocalIffSameParity D.q0 D.q1 D.q3 = refl
fccReciprocalIffSameParity D.q0 D.q2 D.q0 = refl
fccReciprocalIffSameParity D.q0 D.q2 D.q1 = refl
fccReciprocalIffSameParity D.q0 D.q2 D.q2 = refl
fccReciprocalIffSameParity D.q0 D.q2 D.q3 = refl
fccReciprocalIffSameParity D.q0 D.q3 D.q0 = refl
fccReciprocalIffSameParity D.q0 D.q3 D.q1 = refl
fccReciprocalIffSameParity D.q0 D.q3 D.q2 = refl
fccReciprocalIffSameParity D.q0 D.q3 D.q3 = refl
fccReciprocalIffSameParity D.q1 D.q0 D.q0 = refl
fccReciprocalIffSameParity D.q1 D.q0 D.q1 = refl
fccReciprocalIffSameParity D.q1 D.q0 D.q2 = refl
fccReciprocalIffSameParity D.q1 D.q0 D.q3 = refl
fccReciprocalIffSameParity D.q1 D.q1 D.q0 = refl
fccReciprocalIffSameParity D.q1 D.q1 D.q1 = refl
fccReciprocalIffSameParity D.q1 D.q1 D.q2 = refl
fccReciprocalIffSameParity D.q1 D.q1 D.q3 = refl
fccReciprocalIffSameParity D.q1 D.q2 D.q0 = refl
fccReciprocalIffSameParity D.q1 D.q2 D.q1 = refl
fccReciprocalIffSameParity D.q1 D.q2 D.q2 = refl
fccReciprocalIffSameParity D.q1 D.q2 D.q3 = refl
fccReciprocalIffSameParity D.q1 D.q3 D.q0 = refl
fccReciprocalIffSameParity D.q1 D.q3 D.q1 = refl
fccReciprocalIffSameParity D.q1 D.q3 D.q2 = refl
fccReciprocalIffSameParity D.q1 D.q3 D.q3 = refl
fccReciprocalIffSameParity D.q2 D.q0 D.q0 = refl
fccReciprocalIffSameParity D.q2 D.q0 D.q1 = refl
fccReciprocalIffSameParity D.q2 D.q0 D.q2 = refl
fccReciprocalIffSameParity D.q2 D.q0 D.q3 = refl
fccReciprocalIffSameParity D.q2 D.q1 D.q0 = refl
fccReciprocalIffSameParity D.q2 D.q1 D.q1 = refl
fccReciprocalIffSameParity D.q2 D.q1 D.q2 = refl
fccReciprocalIffSameParity D.q2 D.q1 D.q3 = refl
fccReciprocalIffSameParity D.q2 D.q2 D.q0 = refl
fccReciprocalIffSameParity D.q2 D.q2 D.q1 = refl
fccReciprocalIffSameParity D.q2 D.q2 D.q2 = refl
fccReciprocalIffSameParity D.q2 D.q2 D.q3 = refl
fccReciprocalIffSameParity D.q2 D.q3 D.q0 = refl
fccReciprocalIffSameParity D.q2 D.q3 D.q1 = refl
fccReciprocalIffSameParity D.q2 D.q3 D.q2 = refl
fccReciprocalIffSameParity D.q2 D.q3 D.q3 = refl
fccReciprocalIffSameParity D.q3 D.q0 D.q0 = refl
fccReciprocalIffSameParity D.q3 D.q0 D.q1 = refl
fccReciprocalIffSameParity D.q3 D.q0 D.q2 = refl
fccReciprocalIffSameParity D.q3 D.q0 D.q3 = refl
fccReciprocalIffSameParity D.q3 D.q1 D.q0 = refl
fccReciprocalIffSameParity D.q3 D.q1 D.q1 = refl
fccReciprocalIffSameParity D.q3 D.q1 D.q2 = refl
fccReciprocalIffSameParity D.q3 D.q1 D.q3 = refl
fccReciprocalIffSameParity D.q3 D.q2 D.q0 = refl
fccReciprocalIffSameParity D.q3 D.q2 D.q1 = refl
fccReciprocalIffSameParity D.q3 D.q2 D.q2 = refl
fccReciprocalIffSameParity D.q3 D.q2 D.q3 = refl
fccReciprocalIffSameParity D.q3 D.q3 D.q0 = refl
fccReciprocalIffSameParity D.q3 D.q3 D.q1 = refl
fccReciprocalIffSameParity D.q3 D.q3 D.q2 = refl
fccReciprocalIffSameParity D.q3 D.q3 D.q3 = refl

-- The 222 reciprocal index passes the *fcc centring* criterion,
-- but is cancelled by the ideal equal-atom diamond basis. These
-- are distinct mathematical and experimental selection rules.
fccAllows222 : fccPairingsVanish D.q2 D.q2 D.q2 ≡ true
fccAllows222 = refl

idealDiamondExtinguishes222 :
  Diff.norm2 (Diff.eightSiteAmplitude D.q2 D.q2 D.q2) ≡
    Diff.expectedIntensity D.q2 D.q2 D.q2
idealDiamondExtinguishes222 = Diff.exactIntensity D.q2 D.q2 D.q2
