module DASHI.Moonshine.OggSSP2BBinaryTetrahedralCentralSignPhaseNoGoExact where

------------------------------------------------------------------------
-- CENTRAL -1 IS NOT THE COMPLETION10 BINARY PHASE
--
-- Completion10 complement preserves the five-mode quotient and flips only
-- BinaryPhase.  In binary tetrahedral 2T, multiplication by central -1 moves
-- order strata 1 <-> 2 and 3 <-> 6, fixing only order 4.
--
-- Therefore a Mode5 <-> order-stratum recognition cannot simultaneously make
-- Completion10 BinaryPhase equal central-sign multiplication on the strata.
-- The remaining two provenance decisions must come from other sourced data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSP2BBinaryTetrahedralDefectSourceExact as Defect

centralSignOnStratum : Defect.OrderStratum → Defect.OrderStratum
centralSignOnStratum Defect.identity = Defect.centralMinusOne
centralSignOnStratum Defect.centralMinusOne = Defect.identity
centralSignOnStratum Defect.orderFour = Defect.orderFour
centralSignOnStratum Defect.orderThree = Defect.orderSix
centralSignOnStratum Defect.orderSix = Defect.orderThree

centralSignOnStratumInvolutive :
  (s : Defect.OrderStratum) →
  centralSignOnStratum (centralSignOnStratum s) ≡ s
centralSignOnStratumInvolutive Defect.identity = refl
centralSignOnStratumInvolutive Defect.centralMinusOne = refl
centralSignOnStratumInvolutive Defect.orderFour = refl
centralSignOnStratumInvolutive Defect.orderThree = refl
centralSignOnStratumInvolutive Defect.orderSix = refl

data CentralSignFixesIdentityStratum : Set where

centralSignMovesIdentity : CentralSignFixesIdentityStratum → ⊥
centralSignMovesIdentity ()

data CentralSignFixesOrderThreeStratum : Set where

centralSignMovesOrderThree : CentralSignFixesOrderThreeStratum → ⊥
centralSignMovesOrderThree ()

-- Semantic firewall: any proposed provenance argument that equates the
-- Completion10 mode-preserving phase flip with this order-stratum permutation
-- must supply additional structure below the Mode5 quotient; equality on the
-- quotient itself is impossible because central sign moves four strata.
data CompletionModePreservingPhaseIsCentralSignOnStrata : Set where

completionModePreservingPhaseIsNotCentralSignOnStrata :
  CompletionModePreservingPhaseIsCentralSignOnStrata → ⊥
completionModePreservingPhaseIsNotCentralSignOnStrata ()
