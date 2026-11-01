module DASHI.Physics.Closure.Validation.ObservableCollapse where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_)

data ObservableCollapseVerdict : Set where
  collapseEstablished : ObservableCollapseVerdict

record ObservableCollapseHarness : Setω where
  field
    label : String
    Obs : Set
    obs0 : Obs
    obsT : Obs → Obs
    obsFixed : obsT obs0 ≡ obs0
    obsUnique : ∀ o → obsT o ≡ o → o ≡ obs0

record ObservableCollapseFacts (harness : ObservableCollapseHarness) : Setω where
  field
    fixedWitness :
      ObservableCollapseHarness.obsT harness
        (ObservableCollapseHarness.obs0 harness)
      ≡ ObservableCollapseHarness.obs0 harness
    uniquenessWitness :
      ∀ o →
      ObservableCollapseHarness.obsT harness o ≡ o →
      o ≡ ObservableCollapseHarness.obs0 harness

computeFacts : (harness : ObservableCollapseHarness) → ObservableCollapseFacts harness
computeFacts harness =
  record
    { fixedWitness = ObservableCollapseHarness.obsFixed harness
    ; uniquenessWitness = ObservableCollapseHarness.obsUnique harness
    }

classify : ∀ {harness} → ObservableCollapseFacts harness → ObservableCollapseVerdict
classify _ = collapseEstablished
