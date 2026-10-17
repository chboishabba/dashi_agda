module DASHI.Reasoning.JusticeLeeSensibLawRuntimeClosureReceiptRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.SensibLawResidualLattice as SL
import DASHI.Reasoning.JusticeLeeSensibLawBidiSearchClosureExact as Legacy
import DASHI.Reasoning.JusticeLeeSensibLawRuntimeClosureReceiptExact as Closure

sampleAtom : SL.PredicatePNF
sampleAtom =
  SL.predicatePNF
    "sample"
    SL.sig-theme-only
    SL.absent
    (SL.opaqueArg "matter")
    SL.absent
    SL.positive
    SL.directEvidence
    "source:runtime#span=0:6"

sampleEmission : SL.PNFEmissionReceipt
sampleEmission =
  SL.pnfEmissionReceipt
    "parser:runtime"
    "reducer:runtime"
    "source:runtime#span=0:6"
    sampleAtom

sampleRuntimeReceipt : Closure.RuntimePNFControversyReceipt
sampleRuntimeReceipt =
  Closure.runtime-pnf-controversy-receipt
    sampleEmission
    "source-revision:runtime"
    "review-decision:runtime"
    "matter:runtime"
    "controversy:runtime"
    "reverse-search:runtime"
    true refl
    false refl
    false refl
    false refl
    false refl
    "runtime-receipt:sample"

sampleClosure : Closure.ReceiptIndexedLeeRuntimeClosure
sampleClosure =
  Closure.receipt-indexed-lee-runtime-closure
    sampleRuntimeReceipt
    "formal-owner:JusticeLeeSensibLawBidiSearchClosureExact"
    "closure:receipt-indexed"

regression-legacy-global-flag-remains-historical :
  Legacy.LeeSensibLawBidiClosure.actualRuntimeEmissionReceiptAcquired
    Legacy.canonicalLeeSensibLawBidiClosure
  ≡ false
regression-legacy-global-flag-remains-historical = refl

regression-runtime-receipt-does-not-promote-truth :
  Closure.claimTruthPromoted
    (Closure.runtimeReceipt sampleClosure)
  ≡ false
regression-runtime-receipt-does-not-promote-truth = refl

regression-runtime-receipt-does-not-promote-authority :
  Closure.legalAuthorityPromoted
    (Closure.runtimeReceipt sampleClosure)
  ≡ false
regression-runtime-receipt-does-not-promote-authority = refl
