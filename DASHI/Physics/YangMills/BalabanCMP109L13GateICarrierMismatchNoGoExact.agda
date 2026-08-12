module DASHI.Physics.YangMills.BalabanCMP109L13GateICarrierMismatchNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The earlier source-scale no-go proves only that side four does not satisfy
-- Bałaban's L>11 hypothesis.  This file records the stronger same-object
-- consequence for Gate I.  A side-four SU(2) positive-bond tangent carrier has
--
--   3 * 4 * 4^4 = 3072
--
-- scalar coordinates, whereas the minimal source-admissible L=13 carrier has
--
--   3 * 4 * 13^4 = 342732.
--
-- Hence a count-preserving identification of the existing fixed side-four
-- normal/KKT/Hessian carrier with the literal CMP109 L=13 carrier is
-- impossible.  Source-faithful closure must migrate the quantitative local
-- coercivity/normal estimates (or prove a carrier-independent theorem) rather
-- than merely replacing DQ while silently reusing a 3072-coordinate inverse.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

sideFourSiteCount sideFourPositiveBondCount sideFourScalarCoordinateCount : Nat
sideFourSiteCount = 256
sideFourPositiveBondCount = 1024
sideFourScalarCoordinateCount = 3072

l13SiteCount l13PositiveBondCount l13ScalarCoordinateCount : Nat
l13SiteCount = 28561
l13PositiveBondCount = 114244
l13ScalarCoordinateCount = 342732

sideFourCoordinateArithmetic :
  sideFourScalarCoordinateCount ≡ 3 * (4 * sideFourSiteCount)
sideFourCoordinateArithmetic = Agda.Builtin.Equality.refl

l13CoordinateArithmetic :
  l13ScalarCoordinateCount ≡ 3 * (4 * l13SiteCount)
l13CoordinateArithmetic = Agda.Builtin.Equality.refl

data Empty : Set where

sideFourScalarCoordinateCountNotL13 :
  sideFourScalarCoordinateCount ≡ l13ScalarCoordinateCount → Empty
sideFourScalarCoordinateCountNotL13 ()

record CountPreservingGateICarrierIdentification : Set where
  field
    scalarCoordinateCountPreserved :
      sideFourScalarCoordinateCount ≡ l13ScalarCoordinateCount

noCountPreservingSideFourToL13GateIIdentification :
  CountPreservingGateICarrierIdentification → Empty
noCountPreservingSideFourToL13GateIIdentification identification =
  sideFourScalarCoordinateCountNotL13
    (CountPreservingGateICarrierIdentification.scalarCoordinateCountPreserved
      identification)

cmp109L13GateICarrierMismatchLevel : ProofLevel
cmp109L13GateICarrierMismatchLevel = machineChecked

-- The newly generated Path13 LDL certificate is the first migration step.
-- What remains is to lift its one-dimensional floor through the literal L=13
-- four-dimensional gauge/constraint decomposition and rebuild the reduced
-- normal bound on that source-admissible carrier.
cmp109L13ReducedNormalInverseLevel : ProofLevel
cmp109L13ReducedNormalInverseLevel = conditional
