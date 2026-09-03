{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionFiniteL2Round203Exact where

------------------------------------------------------------------------
-- ROUND203B BIDI: GAUGE-INVARIANT WAVEFUNCTIONS -> FINITE SAMPLE PAIRING.
--
-- Supersession correction: the older R197 FiniteSelector is exhaustive and
-- must not be presented as an arbitrary finite ensemble.  The authoritative
-- sample-local carrier is BalabanFiniteSampleObservablePairingRound203Exact.
--
-- A gauge-invariant wavefunction is simply evaluated on the R196 rooted
-- representative at each sampled quotient point.  All conclusions here are
-- sample-local.  No implication is made from sampled norm zero to vanishing on
-- unsampled configurations, and no physical Haar/Gibbs L2 theorem is claimed.
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
import DASHI.Physics.YangMills.BalabanFiniteSampleObservablePairingRound203Exact as Sample
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202

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
  Sample.FiniteSample
    (RootedQuotient {group = group} {base = base} {paths = paths}) →
  R202.BasedGaugeInvariantWavefunction group base →
  R202.BasedGaugeInvariantWavefunction group base →
  ℚ
finiteWavefunctionSamplePairing sample left right =
  Sample.samplePairing sample
    (wavefunctionAsRootedObservable left)
    (wavefunctionAsRootedObservable right)

finiteWavefunctionSampleNormSq :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  Sample.FiniteSample
    (RootedQuotient {group = group} {base = base} {paths = paths}) →
  R202.BasedGaugeInvariantWavefunction group base →
  ℚ
finiteWavefunctionSampleNormSq sample wavefunction =
  finiteWavefunctionSamplePairing sample wavefunction wavefunction

finiteWavefunctionSamplePairingSymmetric :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (sample : Sample.FiniteSample
      (RootedQuotient {group = group} {base = base} {paths = paths}))
    left right →
  finiteWavefunctionSamplePairing sample left right
  ≡ finiteWavefunctionSamplePairing sample right left
finiteWavefunctionSamplePairingSymmetric sample left right =
  Sample.samplePairingSymmetric sample
    (wavefunctionAsRootedObservable left)
    (wavefunctionAsRootedObservable right)

finiteOperatorOutputSampleNormSq :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  Sample.FiniteSample
    (RootedQuotient {group = group} {base = base} {paths = paths}) →
  R202.GaugeInvariantWavefunctionOperator group base →
  R202.BasedGaugeInvariantWavefunction group base →
  ℚ
finiteOperatorOutputSampleNormSq sample operator wavefunction =
  finiteWavefunctionSampleNormSq sample (R202.act operator wavefunction)

wavefunctionFiniteSampleBridgeRound203Level : ProofLevel
wavefunctionFiniteSampleBridgeRound203Level = machineChecked

wavefunctionFiniteSampleSymmetryRound203Level : ProofLevel
wavefunctionFiniteSampleSymmetryRound203Level = machineChecked

literalPhysicalGaugeInvariantL2MeasureRound203Level : ProofLevel
literalPhysicalGaugeInvariantL2MeasureRound203Level = conditional

literalFiniteYMHamiltonianRound203Level : ProofLevel
literalFiniteYMHamiltonianRound203Level = conditional
