module DASHI.Wikimedia.IbrahimDisposableVapeUnknownFeatureLedgerRegression where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

record UnknownFeatureLedgerRegression : Set where
  constructor unknown-feature-ledger-regression
  field
    australianWideMarketReceiptRequired : Bool
    usedHighPuffReactionReceiptRequired : Bool
    confirmedTentativeUnidentifiedSplitRequired : Bool
    sameFeatureAcrossStagesReceiptRequired : Bool
    unknownFeaturesRetainedRequired : Bool
    sameDeviceLifeCycleExperimentRequired : Bool
    priorityAcquisition : String
open UnknownFeatureLedgerRegression public

requiredUnknownFeatureLedgerRegression : UnknownFeatureLedgerRegression
requiredUnknownFeatureLedgerRegression = unknown-feature-ledger-regression
  true true true true true true
  "same-device Australian disposable: virgin liquid -> early/mid/late aerosol + liquid -> spent materials with non-target feature tracking"
