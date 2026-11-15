module DASHI.Physics.Plasma.Phase243FreeBoundarySixRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Plasma.Phase243FreeBoundarySixExact as FB6

candidateCountPinned : Nat
candidateCountPinned = FB6.candidateCount

candidateCountPinnedIsSix : candidateCountPinned ≡ 6
candidateCountPinnedIsSix = refl

frozenPinned : Bool
frozenPinned = FB6.sixCandidateIdentitiesFrozen FB6.canonicalFreeBoundarySixBoundary

frozenPinnedIsTrue : frozenPinned ≡ true
frozenPinnedIsTrue = refl

proxyNotEquilibriumPinned : Bool
proxyNotEquilibriumPinned = FB6.proxyMetricsAreFreeBoundarySolutions FB6.canonicalFreeBoundarySixBoundary

proxyNotEquilibriumPinnedIsFalse : proxyNotEquilibriumPinned ≡ false
proxyNotEquilibriumPinnedIsFalse = refl

solveOrRejectPinned : Bool
solveOrRejectPinned = FB6.eachCandidateMustSolveOrReject FB6.canonicalFreeBoundarySixBoundary

solveOrRejectPinnedIsTrue : solveOrRejectPinned ≡ true
solveOrRejectPinnedIsTrue = refl
