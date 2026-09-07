module DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core

private
  boundary = Core.canonicalFinalPoleQuotientAnalyticCoreBoundary

offCoreIsOnlyBudgetFitMath :
  Core.offAnalyticCoreContainsOnlyBudgetFitMathematics boundary ≡ true
offCoreIsOnlyBudgetFitMath = refl

gammaCoreIsOnlyBudgetFitMath :
  Core.gammaAnalyticCoreContainsOnlyBudgetFitMathematics boundary ≡ true
gammaCoreIsOnlyBudgetFitMath = refl

cutoffIdentityIsRepresentation :
  Core.cutoffIdentityIsSeparateFromOffAnalysis boundary ≡ true
cutoffIdentityIsRepresentation = refl

taperIdentityIsRepresentation :
  Core.taperIdentityIsSeparateFromBothAnalyticCores boundary ≡ true
taperIdentityIsRepresentation = refl

coresCompileHistoricalPayments :
  Core.analyticCoresPlusAttachmentsCompileExistingPayments boundary ≡ true
coresCompileHistoricalPayments = refl

offCoreStillOpen : Core.offAnalyticCoreInhabitedHere boundary ≡ false
offCoreStillOpen = refl

gammaCoreStillOpen : Core.gammaAnalyticCoreInhabitedHere boundary ≡ false
gammaCoreStillOpen = refl

rhStillOpen : Core.rhDerived boundary ≡ false
rhStillOpen = refl
