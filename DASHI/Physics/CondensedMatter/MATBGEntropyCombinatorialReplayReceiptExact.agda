module DASHI.Physics.CondensedMatter.MATBGEntropyCombinatorialReplayReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record EntropyCombinatorialReplayReceipt : Set where
  constructor entropy-combinatorial-replay-receipt
  field
    scriptPath : String
    evidencePath : String
    scriptSHA256 : String
    sourceDOI : String
    filling0HighSOverKB : String
    filling1HighSOverKB : String
    filling2HighSOverKB : String
    filling3HighSOverKB : String
    filling0LowSOverKB : String
    filling1LowSOverKB : String
    filling2LowSOverKB : String
    filling3LowSOverKB : String
    assertionsPassed : Bool

open EntropyCombinatorialReplayReceipt public

canonicalEntropyCombinatorialReplayReceipt : EntropyCombinatorialReplayReceipt
canonicalEntropyCombinatorialReplayReceipt =
  entropy-combinatorial-replay-receipt
    "scripts/matbg_entropy_combinatorial_replay.py"
    "Docs/evidence/matbg_entropy_combinatorial_replay_2026-10-16.json"
    "88f8df07a88df1c7e548dbd6d8a982b3e3ed83f8465ea99ae46597bb201e156e"
    "10.1038/s41467-026-76179-y"
    "4.248495242049359"
    "4.02535169073515"
    "3.332204510175204"
    "2.0794415416798357"
    "0.0"
    "1.3862943611198906"
    "1.791759469228055"
    "1.3862943611198906"
    true

record EntropyCombinatorialReplayBoundary : Set where
  constructor entropy-combinatorial-replay-boundary
  field
    sourceCombinatorialFormulasPaid : Bool
    exactMicrostateCountsPaid : Bool
    combinatorialLogarithmReplayPaid : Bool
    deltaEntropyReplayPaid : Bool
    measuredEntropyCurveReplayPaid : Bool
    sameSampleQTMEntropyPaid : Bool
    microscopicMechanismProved : Bool
    agdaKernelReceiptPaid : Bool

open EntropyCombinatorialReplayBoundary public

canonicalEntropyCombinatorialReplayBoundary : EntropyCombinatorialReplayBoundary
canonicalEntropyCombinatorialReplayBoundary =
  entropy-combinatorial-replay-boundary
    true true true true false false false false

record EntropyCombinatorialReplayAttributionBoundary : Set where
  constructor entropy-combinatorial-replay-attribution-boundary
  field
    zhangEtAlOwnEntropyFormulaAndExperimentalComparison : Bool
    dashiOwnsNumericalCombinatorialReplay : Bool
    modelTargetReplayIsNotExperimentalCurveReplay : Bool

open EntropyCombinatorialReplayAttributionBoundary public

canonicalEntropyCombinatorialReplayAttributionBoundary : EntropyCombinatorialReplayAttributionBoundary
canonicalEntropyCombinatorialReplayAttributionBoundary =
  entropy-combinatorial-replay-attribution-boundary true true true
