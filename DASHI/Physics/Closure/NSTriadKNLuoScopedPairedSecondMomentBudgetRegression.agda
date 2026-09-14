module DASHI.Physics.Closure.NSTriadKNLuoScopedPairedSecondMomentBudgetRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoScopedPairedSecondMomentBudgetExact as Scoped

scopedBudgetClosed :
  Scoped.scopedPairedSecondMomentCompilerClosed ≡ true
scopedBudgetClosed = refl

oldUniversalInterfaceRetainedAsHistorical :
  Scoped.oldUniversalPairedSecondMomentBudgetRetained ≡ true
oldUniversalInterfaceRetainedAsHistorical = refl

scopedBudgetDoesNotCloseUniformPhysicalProducer :
  Scoped.scopedBudgetClosesCutoffUniformPhysicalProducer ≡ false
scopedBudgetDoesNotCloseUniformPhysicalProducer = refl
