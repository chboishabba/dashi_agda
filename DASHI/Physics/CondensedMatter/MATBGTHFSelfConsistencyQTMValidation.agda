module DASHI.Physics.CondensedMatter.MATBGTHFSelfConsistencyQTMValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGTHFSelfConsistencyQTMExact as THFQTM

self-consistency-equations-paid : THFQTM.selfConsistencyEquationsSourcePaid THFQTM.canonicalTHFSelfConsistencyQTMBoundary ≡ true
self-consistency-equations-paid = refl

qtm-current-contract-paid : THFQTM.qtmGoldenRuleObserverSourcePaid THFQTM.canonicalTHFSelfConsistencyQTMBoundary ≡ true
qtm-current-contract-paid = refl

qtm-electrostatics-source-paid : THFQTM.qtmElectrostaticsSourcePaid THFQTM.canonicalTHFSelfConsistencyQTMBoundary ≡ true
qtm-electrostatics-source-paid = refl

full-solve-remains-open : THFQTM.fullSelfConsistentNumericalSolvePaid THFQTM.canonicalTHFSelfConsistencyQTMBoundary ≡ false
full-solve-remains-open = refl

experimental-replay-remains-open : THFQTM.qtmExperimentalDataReplayPaid THFQTM.canonicalTHFSelfConsistencyQTMBoundary ≡ false
experimental-replay-remains-open = refl
