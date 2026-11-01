module DASHI.Analysis.Maass.ValidatedNumericsArtifact where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.HejhalAutomorphyResidual as HAR

------------------------------------------------------------------------
-- A byte/digest-bound validated-numerics boundary.  There are deliberately
-- no string-valued numerical witnesses here: acceptance is connected to the
-- internal analytic proposition by checkerSound.

record MaassAnalyticBounds
  (Γ : MFC.ΓMaass)
  (state : MFC.TruncatedFourierState Γ) : Set₁ where
  field
    residualEnclosure : HAR.ResidualEnclosure Γ state
    samplingBound : Set
    automorphyBound : Set
    cuspTailBound : Set
    operatorBound : Set
    normalizationNonzero : Set

record MaassValidatedNumericsArtifact
  {Γ : MFC.ΓMaass}
  (state : MFC.TruncatedFourierState Γ)
  (Bytes Digest Payload : Set) : Setω where
  field
    sourceCommit : Digest
    cleanWorktreeWitness : Set
    runnerDigest : Digest
    inputDigest : Digest
    outputDigest : Digest
    frozenBytes : Bytes
    precision : Nat
    intervalPayload : Payload
    parser : Bytes → Payload
    parserAcceptedFrozenOutput : parser frozenBytes ≡ intervalPayload
    checker : Payload → Bool
    checkerPassed : checker intervalPayload ≡ true
    checkerSound :
      checker intervalPayload ≡ true → MaassAnalyticBounds Γ state

open MaassValidatedNumericsArtifact public
