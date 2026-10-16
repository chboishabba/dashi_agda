module DASHI.Physics.CondensedMatter.MATBGEntropyMaxwellReplayContractExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-FAITHFUL MAXWELL ENTROPY REPLAY KERNEL
--
-- Zhang et al. 2026, DOI 10.1038/s41467-026-76179-y, Methods:
--   (∂S/∂ν)_T = -(∂μ/∂T)_ν
--   S(ν,T) = -∫_4^ν (∂μ/∂T)_ν dν
-- with the preferred numerical ordering
--   S(ν,T) = -∂_T ∫_4^ν μ(ν,T) dν,
-- and a three-adjacent-temperature linear fit for ∂/∂T.
--
-- The associated executable receipt validates this algorithm against a
-- synthetic analytic fixture. It does not use the publisher XLSX data and
-- therefore does not claim measured entropy replay.
------------------------------------------------------------------------

record EntropyMaxwellSourceAlgorithmReceipt : Set where
  constructor entropy-maxwell-source-algorithm-receipt
  field
    sourceDOI : String
    maxwellRelation : String
    entropyBoundary : String
    preferredIntegrationDerivativeOrder : String
    temperatureDerivativeRule : String

open EntropyMaxwellSourceAlgorithmReceipt public

canonicalEntropyMaxwellSourceAlgorithmReceipt : EntropyMaxwellSourceAlgorithmReceipt
canonicalEntropyMaxwellSourceAlgorithmReceipt =
  entropy-maxwell-source-algorithm-receipt
    "10.1038/s41467-026-76179-y"
    "dS/dnu = -dmu/dT"
    "S(nu=4,T)=0"
    "S(nu,T) = -d/dT integral_4^nu mu(nu,T) dnu"
    "linear fit over three adjacent temperature points"

record EntropyMaxwellReplayReceipt : Set where
  constructor entropy-maxwell-replay-receipt
  field
    producer : String
    evidence : String
    analyticFixtureEntropyAtNu0MeVPerK : String
    maxAbsoluteError : String
    sourceAlgorithmExecutionPaid : Bool
    experimentalWorkbookBytesUsed : Bool
    measuredEntropyReplayPaid : Bool
    sameSampleQTMEntropyPaid : Bool

open EntropyMaxwellReplayReceipt public

canonicalEntropyMaxwellReplayReceipt : EntropyMaxwellReplayReceipt
canonicalEntropyMaxwellReplayReceipt =
  entropy-maxwell-replay-receipt
    "scripts/matbg_entropy_maxwell_replay_contract.py"
    "Docs/evidence/matbg_entropy_maxwell_replay_contract_2026-10-16.json"
    "0.008"
    "8.673617379884035e-19"
    true false false false

record EntropyMaxwellReplayBoundary : Set where
  constructor entropy-maxwell-replay-boundary
  field
    sourceEquationsPaid : Bool
    sourceBoundaryConditionPaid : Bool
    threePointFitRulePaid : Bool
    syntheticReplayNumericallyExecuted : Bool
    experimentalDataAdapterPaid : Bool
    experimentalEntropyReplayPaid : Bool
    sameSampleQTMEntropyPaid : Bool
    syntheticFixtureDoesNotCreateExperimentalAuthority : Bool

open EntropyMaxwellReplayBoundary public

canonicalEntropyMaxwellReplayBoundary : EntropyMaxwellReplayBoundary
canonicalEntropyMaxwellReplayBoundary =
  entropy-maxwell-replay-boundary true true true true false false false true
