module DASHI.Mathematics.Algebra.RationalAlbertJordanFrontierExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanUnitExact as U

------------------------------------------------------------------------
-- Consolidated status after constructing the rational Albert carrier.
--
-- The carrier/product/unit/cubic norm are literal repo objects.  The unit laws
-- are theorem-facing.  The Jordan identity and exceptional automorphism/
-- stabilizer actions remain explicit leaves and are not inferred from Python
-- preflight or standard mathematical nomenclature.
------------------------------------------------------------------------

leftUnitPaid : (x : A.RationalAlbert) →
  A.jordanProduct A.albertUnit x ≡ x
leftUnitPaid = U.leftUnit

rightUnitPaid : (x : A.RationalAlbert) →
  A.jordanProduct x A.albertUnit ≡ x
rightUnitPaid = U.rightUnit

record RationalAlbertFrontier : Set where
  constructor rationalAlbertFrontier
  field
    carrier27Constructed : Bool
    productConstructed : Bool
    unitConstructed : Bool
    twoSidedUnitTheoremSourceWritten : Bool
    cubicNormConstructed : Bool
    pythonJordanIdentityPreflightPassed : Bool
    pythonCharacteristicIdentityPreflightPassed : Bool
    pythonPreflightCountsAsKernelProof : Bool
    universalJordanIdentityKernelProved : Bool
    cubicCharacteristicIdentityKernelProved : Bool
    f4AutomorphismRecognitionInhabited : Bool
    e6CubicNormStabilizerRecognitionInhabited : Bool

open RationalAlbertFrontier public

currentRationalAlbertFrontier : RationalAlbertFrontier
currentRationalAlbertFrontier =
  rationalAlbertFrontier
    true true true true true
    true true false
    false false false false
