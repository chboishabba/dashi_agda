{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionFiniteSampleRound205Exact where

------------------------------------------------------------------------
-- ROUND205 BIDI: R202 GAUGE-INVARIANT WAVEFUNCTIONS -> R203 FINITE SAMPLE.
--
-- R203 corrected the finite-carrier semantics: a finite list of rooted quotient
-- points is only a sample, whereas the older FiniteSelector is exhaustive.
-- This module therefore performs only the literal safe bridge: evaluate each
-- R202 invariant wavefunction on the sampled R196 rooted representatives.
--
-- No sample is promoted to the physical configuration-space L2 carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanFinitePhysicalGaugeQuotientCarrierRound196Exact as R196
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202
import DASHI.Physics.YangMills.BalabanFiniteSampleObservablePairingRound203Exact as R203

RootedQuotient :
  ∀ {N : Nat} {{_ : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} → Set
RootedQuotient {group = group} {base = base} {paths = paths} =
  R196.FiniteRootedGaugeQuotientCarrier group base paths

wavefunctionAsRootedObservable :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  R202.BasedGaugeInvariantWavefunction group base →
  RootedQuotient {group = group} {base = base} {paths = paths} → ℚ
wavefunctionAsRootedObservable wavefunction quotient =
  R202.evaluateOnRootedQuotient wavefunction quotient

finiteWavefunctionSamplePairing :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  R203.FiniteSample
    (RootedQuotient {group = group} {base = base} {paths = paths}) →
  R202.BasedGaugeInvariantWavefunction group base →
  R202.BasedGaugeInvariantWavefunction group base →
  ℚ
finiteWavefunctionSamplePairing sample left right =
  R203.samplePairing sample
    (wavefunctionAsRootedObservable left)
    (wavefunctionAsRootedObservable right)

finiteWavefunctionSampleNormSq :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  R203.FiniteSample
    (RootedQuotient {group = group} {base = base} {paths = paths}) →
  R202.BasedGaugeInvariantWavefunction group base → ℚ
finiteWavefunctionSampleNormSq sample wavefunction =
  finiteWavefunctionSamplePairing sample wavefunction wavefunction

finiteWavefunctionSamplePairingSymmetric :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (sample : R203.FiniteSample
      (RootedQuotient {group = group} {base = base} {paths = paths}))
    left right →
  finiteWavefunctionSamplePairing sample left right
  ≡ finiteWavefunctionSamplePairing sample right left
finiteWavefunctionSamplePairingSymmetric sample left right =
  R203.samplePairingSymmetric sample
    (wavefunctionAsRootedObservable left)
    (wavefunctionAsRootedObservable right)

finiteOperatorOutputSampleNormSq :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  R203.FiniteSample
    (RootedQuotient {group = group} {base = base} {paths = paths}) →
  R202.GaugeInvariantWavefunctionOperator group base →
  R202.BasedGaugeInvariantWavefunction group base → ℚ
finiteOperatorOutputSampleNormSq sample operator wavefunction =
  finiteWavefunctionSampleNormSq sample (R202.act operator wavefunction)

wavefunctionFiniteSampleBridgeRound205Level : ProofLevel
wavefunctionFiniteSampleBridgeRound205Level = machineChecked

wavefunctionFiniteSamplePairingSymmetryRound205Level : ProofLevel
wavefunctionFiniteSamplePairingSymmetryRound205Level = machineChecked

literalPhysicalGaugeInvariantL2MeasureRound205Level : ProofLevel
literalPhysicalGaugeInvariantL2MeasureRound205Level = conditional
