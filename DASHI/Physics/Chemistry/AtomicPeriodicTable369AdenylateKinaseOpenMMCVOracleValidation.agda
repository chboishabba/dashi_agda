module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseOpenMMCVOracleValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseOpenMMCVOracleExact as Oracle

boundary = Oracle.canonicalAdKOpenMMCVOracleBoundary

_ : Oracle.openMMCentroidCapabilityRetained boundary ≡ true
_ = refl

_ : Oracle.sameConfigurationComparisonRequired boundary ≡ true
_ = refl

_ : Oracle.toleranceMustBeDeclared boundary ≡ true
_ = refl

_ : Oracle.openMMAgreementCreatesFormalAuthority boundary ≡ false
_ = refl

_ : Oracle.comparisonExecutionPaidHere boundary ≡ false
_ = refl
