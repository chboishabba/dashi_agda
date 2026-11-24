{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMFiniteExteriorFactorCancellationSourceOnlyExact where

------------------------------------------------------------------------
-- SOURCE / STATUS
--
-- Finite algebraic core of the exterior-factor cancellation check listed in
-- Docs/roadmaps/ClayRecoveredProducersW2NoGoR856SourceMaxCut20261115.md:282
-- and Docs/roadmaps/ClaySixFrontierABCExactGates20261114.json:3743-3755.
-- This is only a finite rational sum-scaling identity.  It does not instantiate
-- SU(N) Haar Wilson measure, blocked-vs-bare local TV, R445, D1/D2, or Clay.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

finiteExteriorFactorScalesSum :
  ∀ {A B : Set} (interior : List A) (w : A → ℚ)
    (outside : B → ℚ) (y : B) →
    Sums.sumRational interior (λ z → outside y * w z)
    ≡ outside y * Sums.sumRational interior w
finiteExteriorFactorScalesSum interior w outside y =
  Sums.sumRationalScale (outside y) interior w

finiteExteriorCancellationCompilerLevel : ProofLevel
finiteExteriorCancellationCompilerLevel = machineChecked
