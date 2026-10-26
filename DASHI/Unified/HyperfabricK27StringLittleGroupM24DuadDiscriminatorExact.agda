module DASHI.Unified.HyperfabricK27StringLittleGroupM24DuadDiscriminatorExact where

-- ORIGINAL MATHEMATICS / SOURCES:
-- Standard 26D critical bosonic-string massless spectrum:
-- SO(24) physical transverse h_(ij)^TF 299, B_[ij] 276, Phi 1.
-- Transverse Hodge star gives Λ²(R²⁴) <-> Λ²²(R²⁴), dimension 276.
-- M24 ATLAS 24-point action 2A: fixed 8, swaps 8; ATLAS p276
-- duad action 2A: fixed 36. Its NATURAL exterior-square action on
-- oriented 2-tensors has character C(8,2)-8=20, NOT 36.
--
-- Hence M24 p276 and restricted Λ²(24) are nonisomorphic as
-- characteristic-zero representations with the natural point action.
-- This source-count theorem is not an M24 generator/permutation proof
-- in Agda, nor a K27/VOA/string Hilbert-space identification.
--
-- REUSE: original Leech weight-two 24D symmetric-coordinate counting
-- and original M24 p276 source/duad authority; no duplicate M24 model.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Moonshine.LeechWeightTwo196608BridgeExact as Leech
import DASHI.Moonshine.OggSSP2BM24DuadPair24AuthorityExact as Duads

physicalTransverseDimension : Nat
physicalTransverseDimension = 24

criticalBosonicTargetDimension : Nat
criticalBosonicTargetDimension = 26

sourceDimension26Is24Plus2 :
  criticalBosonicTargetDimension ≡ physicalTransverseDimension + 2
sourceDimension26Is24Plus2 = refl

masslessGravitonPolarizations : Nat
masslessGravitonPolarizations = 299

masslessBTwoPolarizations : Nat
masslessBTwoPolarizations = 276

masslessDualCTwentyTwoPolarizations : Nat
masslessDualCTwentyTwoPolarizations = 276

masslessDilatonPolarizations : Nat
masslessDilatonPolarizations = 1

bosonicClosedTensorProduct : Nat
bosonicClosedTensorProduct = 24 * 24

masslessPhysicalSpectrumCount :
  masslessGravitonPolarizations + masslessBTwoPolarizations +
  masslessDilatonPolarizations ≡ bosonicClosedTensorProduct
masslessPhysicalSpectrumCount = refl

sourceLeechTraceFreeSymmetric299 :
  Leech.traceFreeSymmetricSquareCount ≡ masslessGravitonPolarizations
sourceLeechTraceFreeSymmetric299 =
  Leech.traceFreeSymmetricSquareCountIs299

sourceM24Duad276 :
  Duads.duadCount ≡ masslessBTwoPolarizations
sourceM24Duad276 = Duads.duadCountIs276

dualTwentyTwoSameDegree :
  masslessDualCTwentyTwoPolarizations ≡ masslessBTwoPolarizations
dualTwentyTwoSameDegree = refl

-- ATLAS M24 2A on 24 points has 1^8 2^8.
-- On unordered duads: C(8,2) fixed pairs + 8 swapped pairs =36.
sourceAtlas2AFixedDuads : 28 + 8 ≡ 36
sourceAtlas2AFixedDuads = refl

-- On oriented Λ², the 8 swapped pairs have sign -1:
-- C(8,2) - 8 = 20. Avoid negative integers in this Nat-only receipt.
source2AWedgeTrace : 20 + 8 ≡ 28
source2AWedgeTrace = refl

-- The two traces cannot agree, so a conjugating equivariant
-- characteristic-zero linear isomorphism preserving the given
-- M24 action CANNOT exist (trace similarity is established linear algebra
-- prior art; no representation constructor is claimed here).
twoACharacterMismatch : 36 ≡ 20 → ⊥
twoACharacterMismatch ()

-- Important WrongType:
--   M24 permutation degree-276 != antisymmetric SO24 B-field action
--   != unverified Carnahan-Urano Tate module 276.
-- The Leech trace-free symmetric-square 299 has matching size but no
-- automatically selected physical string graviton observable either.
