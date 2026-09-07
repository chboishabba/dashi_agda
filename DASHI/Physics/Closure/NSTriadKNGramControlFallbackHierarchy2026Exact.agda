module DASHI.Physics.Closure.NSTriadKNGramControlFallbackHierarchy2026Exact where

------------------------------------------------------------------------
-- 2026 NS GRAM CONTROL FALLBACK HIERARCHY
--
-- Source calibration:
--   RequestProject/NavierStokes/AlmostOrthogonalGramSchur.lean
--   (Lean sibling module supplied in the 2026-09-06 handoff archive;
--   no stable repository commit identifier was present in this archive).
--
--   Mischa Cotlar; Elias M. Stein,
--   "A unified theory of Hilbert transforms and ergodic theorems" (1955).
--   No DOI is known for the cited conference article.
--
-- DASHI extension:
--   Separate four logical levels which had previously been easy to conflate:
--
--     pairwise Cauchy--Schwarz
--       < absolute-coherence Schur
--       < block/operator cancellation
--       < direct signed resolvent control.
--
-- Failure of a stronger *producer* is not, by itself, failure of the downstream
-- resolvent programme: a weaker certificate may still inhabit the consumer.
-- This file makes that fail-open search logic proof-bearing.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Search levels, ordered by how much cancellation/structure they retain.
------------------------------------------------------------------------

data GramControlLevel : Set where
  pairwiseCS : GramControlLevel
  absoluteSchur : GramControlLevel
  blockOperator : GramControlLevel
  signedResolvent : GramControlLevel

------------------------------------------------------------------------
-- Certificate/refutation carriers.  They are deliberately distinct types:
-- a refutation of one candidate route cannot be pattern-matched as a global
-- impossibility theorem.
------------------------------------------------------------------------

data AbsoluteSchurCertificate : Set where
  absolute-schur-certificate : AbsoluteSchurCertificate

data AbsoluteSchurRefuted : Set where
  absolute-schur-refuted : AbsoluteSchurRefuted

data BlockOperatorCertificate : Set where
  block-operator-certificate : BlockOperatorCertificate

data BlockOperatorRefuted : Set where
  block-operator-refuted : BlockOperatorRefuted

data SignedResolventCertificate : Set where
  signed-resolvent-certificate : SignedResolventCertificate

data ResolventRouteViable : Set where
  viable-via-absolute-schur : AbsoluteSchurCertificate → ResolventRouteViable
  viable-via-block-operator : BlockOperatorCertificate → ResolventRouteViable
  viable-via-signed-resolvent : SignedResolventCertificate → ResolventRouteViable

absoluteSchurFailureDoesNotKillBlockRoute :
  AbsoluteSchurRefuted → BlockOperatorCertificate → ResolventRouteViable
absoluteSchurFailureDoesNotKillBlockRoute _ block =
  viable-via-block-operator block

absoluteAndBlockFailureDoNotKillSignedRoute :
  AbsoluteSchurRefuted →
  BlockOperatorRefuted →
  SignedResolventCertificate →
  ResolventRouteViable
absoluteAndBlockFailureDoNotKillSignedRoute _ _ signed =
  viable-via-signed-resolvent signed

------------------------------------------------------------------------
-- Coherent-family obstruction has exactly the intended scope: it refutes a
-- truncation-uniform absolute-row-sum producer when coherence forces the row
-- mass to grow.  It is not typed as a block/signed no-go.
------------------------------------------------------------------------

data PerfectCoherenceObstruction : Set where
  perfect-coherence-obstruction : PerfectCoherenceObstruction

coherentObstructionTargetsAbsoluteSchur :
  PerfectCoherenceObstruction → AbsoluteSchurRefuted
coherentObstructionTargetsAbsoluteSchur _ = absolute-schur-refuted

------------------------------------------------------------------------
-- Fixed-output testing protocol requested in the cross-pollination:
--
--   1. absolute normalized Gram row mass;
--   2. block operator interaction;
--   3. actual signed resolvent quadratic form.
------------------------------------------------------------------------

data GramDiagnostic : Set where
  absoluteNormalizedRowMass : GramDiagnostic
  blockOperatorMass : GramDiagnostic
  signedResolventQuadraticForm : GramDiagnostic

firstDiagnostic : GramDiagnostic
firstDiagnostic = absoluteNormalizedRowMass

fallbackAfterAbsoluteFailure : GramDiagnostic
fallbackAfterAbsoluteFailure = blockOperatorMass

fallbackAfterBlockFailure : GramDiagnostic
fallbackAfterBlockFailure = signedResolventQuadraticForm

------------------------------------------------------------------------
-- Honest programme state.
------------------------------------------------------------------------

absoluteSchurIsSufficientNotNecessary : Bool
absoluteSchurIsSufficientNotNecessary = true

largeAbsoluteRowMassImpliesResolventDead : Bool
largeAbsoluteRowMassImpliesResolventDead = false

largeBlockMassImpliesSignedFormLarge : Bool
largeBlockMassImpliesSignedFormLarge = false

coherentPhysicalExampleRefutesThatAbsoluteProducer : Bool
coherentPhysicalExampleRefutesThatAbsoluteProducer = true

absoluteSchurIsSufficientNotNecessaryIsTrue :
  absoluteSchurIsSufficientNotNecessary ≡ true
absoluteSchurIsSufficientNotNecessaryIsTrue = refl

largeAbsoluteRowMassImpliesResolventDeadIsFalse :
  largeAbsoluteRowMassImpliesResolventDead ≡ false
largeAbsoluteRowMassImpliesResolventDeadIsFalse = refl

largeBlockMassImpliesSignedFormLargeIsFalse :
  largeBlockMassImpliesSignedFormLarge ≡ false
largeBlockMassImpliesSignedFormLargeIsFalse = refl
