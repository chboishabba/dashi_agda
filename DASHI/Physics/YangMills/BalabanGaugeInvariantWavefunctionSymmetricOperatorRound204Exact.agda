{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionSymmetricOperatorRound204Exact where

------------------------------------------------------------------------
-- ROUND204 BIDI: SAMPLE-LOCAL SYMMETRY ON THE CORRECT HAMILTONIAN TYPE.
--
-- R202 puts H on gauge-invariant wavefunctions.  R203B evaluates those
-- wavefunctions on an explicitly finite SAMPLE of R196 rooted quotient points.
-- No finite sample is promoted to an exhaustive configuration-space carrier.
--
-- On this deliberately local carrier, operator symmetry is exactly
--
--   <H f , g>_sample = <f , H g>_sample.
--
-- Quotient compatibility is automatic because H returns another based-gauge-
-- invariant wavefunction.  Physical Haar/Gibbs L2 symmetry remains separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanFinitePhysicalGaugeQuotientCarrierRound196Exact as R196
import DASHI.Physics.YangMills.BalabanFiniteSampleObservablePairingRound203Exact as Sample
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionFiniteL2Round203Exact as R203

record FiniteSampleSymmetricGaugeInvariantOperator
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (sample : Sample.FiniteSample
      (R203.RootedQuotient {group = group} {base = base} {paths = paths})) : Set₁ where
  field
    operator : R202.GaugeInvariantWavefunctionOperator group base

    symmetricOnSample :
      ∀ left right →
      R203.finiteWavefunctionSamplePairing sample
        (R202.act operator left) right
      ≡ R203.finiteWavefunctionSamplePairing sample
          left (R202.act operator right)

open FiniteSampleSymmetricGaugeInvariantOperator public

sampleSymmetricOperatorNormalizationHandoff :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    {sample : Sample.FiniteSample
      (R203.RootedQuotient {group = group} {base = base} {paths = paths})}
    (symmetricOperator :
      FiniteSampleSymmetricGaugeInvariantOperator group base paths sample)
    wavefunction field →
  R202.amplitude
    (R202.act (operator symmetricOperator) wavefunction) field
  ≡ R202.evaluateOnRootedQuotient
      (R202.act (operator symmetricOperator) wavefunction)
      (R196.normalizeToFiniteRootedGaugeQuotient group base paths field)
sampleSymmetricOperatorNormalizationHandoff symmetricOperator wavefunction =
  R202.operatorNormalizationHandoff (operator symmetricOperator) wavefunction

finiteSampleSymmetricGaugeInvariantOperatorRound204Level : ProofLevel
finiteSampleSymmetricGaugeInvariantOperatorRound204Level = machineChecked

-- These are intentionally stronger than sample symmetry and remain live.
literalPhysicalYMHamiltonianProducerRound204Level : ProofLevel
literalPhysicalYMHamiltonianProducerRound204Level = conditional

literalPhysicalYMHamiltonianSymmetryRound204Level : ProofLevel
literalPhysicalYMHamiltonianSymmetryRound204Level = conditional

literalPhysicalGaugeInvariantL2CompletionRound204Level : ProofLevel
literalPhysicalGaugeInvariantL2CompletionRound204Level = conditional
