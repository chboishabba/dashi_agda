module DASHI.Physics.YangMills.BalabanRootedPositiveFormGNSCompilerRound202Exact where

------------------------------------------------------------------------
-- ROUND 202
--
-- Pure compiler eliminating one terminal bookkeeping seam.
--
-- Given the rooted normal-form map and a positive form whose null predicate
-- is zero diagonal norm, construct the R200 same-carrier physical/GNS bridge
-- definitionally.  No additional quotient or null-equivalence theorem is
-- required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanRootedPhysicalQuotientGNSBridgeRound200Exact as R200
import DASHI.Physics.YangMills.BalabanRootedPhysicalQuotientPositiveFormRound201Exact as R201

compileRootedPositiveFormToGNSBridge :
  ∀ {Configuration Rooted Scalar}
    (normalise : Configuration → Rooted)
    (form : R201.RootedPositiveForm Rooted Scalar) →
  R200.RootedPhysicalQuotientGNSBridge Configuration Rooted Scalar
compileRootedPositiveFormToGNSBridge {Rooted = Rooted} normalise form = record
  { normalise = normalise
  ; GNSCarrier = Rooted
  ; sameCarrier = refl
  ; zero = R201.zero form
  ; normSquared = R201.normSquared form
  ; PhysicalNull = R201.Null form
  ; GNSNull = R201.Null form
  ; gnsNullOnRooted = R201.Null form
  ; gnsNullOnRootedIsPhysicalNull = λ x → refl
  ; physicalNullIsZeroNorm = R201.rootedNullIsZeroNorm form
  }
