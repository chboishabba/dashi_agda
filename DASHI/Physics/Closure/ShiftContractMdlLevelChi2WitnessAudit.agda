module DASHI.Physics.Closure.ShiftContractMdlLevelChi2WitnessAudit where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftLibrary as LIB
open import DASHI.Physics.Closure.ShiftContractMdlLevelCounterexampleAudit as SCMA
  using (oldCoarsePairSeparatedByMdlLevelSurface)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (ShiftContractMdlLevelCoarseObservablePackage; canonicalShiftContractMdlLevelCoarseObservablePackage; π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using (coarseCounterexampleLeft; coarseCounterexampleRight)

------------------------------------------------------------------------
-- Chi2-boundary witness audit for the strengthened `mdlLevel × π-max`
-- surface.
--
-- The explicit chi2 examples are a bounded witness pool, but they live in
-- the ternary-real validation carrier rather than the shift-contract
-- carrier.  So this audit packages the strongest clean result available:
-- the old coarse counterexample pair is rejected by the strengthened
-- surface, while the chi2 pool itself is recorded as carrier-mismatched for
-- direct `ShiftContractState` comparison.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

data Chi2WitnessAuditOutcome : Set where
  poolCarrierMismatch : Chi2WitnessAuditOutcome

record ShiftContractMdlLevelChi2WitnessAudit : Set₁ where
  field
    poolCount : Nat
    primary : LIB.Chi2BoundaryCase
    secondary : LIB.Chi2BoundaryCase
    tertiary : LIB.Chi2BoundaryCase
    retiredPairRejected :
      π-mdl-max OB.coarseCounterexampleLeft
        ≢
      π-mdl-max OB.coarseCounterexampleRight
    outcome : Chi2WitnessAuditOutcome

canonicalShiftContractMdlLevelChi2WitnessAudit :
  ShiftContractMdlLevelChi2WitnessAudit
canonicalShiftContractMdlLevelChi2WitnessAudit =
  record
    { poolCount = LIB.caseCount
    ; primary = LIB.caseA
    ; secondary = LIB.caseB
    ; tertiary = LIB.caseC
    ; retiredPairRejected = oldCoarsePairSeparatedByMdlLevelSurface
    ; outcome = poolCarrierMismatch
    }

open ShiftContractMdlLevelChi2WitnessAudit public
