{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionFiniteL2Round203Exact where

------------------------------------------------------------------------
-- ROUND203 BIDI: WAVEFUNCTION HAMILTONIAN CARRIER -> EXISTING ROOTED FINITE L2.
--
-- R202 corrects the semantic carrier: the Hamiltonian acts on gauge-invariant
-- wavefunctions, not on gauge fields. R197 already owns an exact finite
-- selected-ensemble pairing on the R196 rooted quotient. The bridge is literal:
-- evaluate a gauge-invariant wavefunction on each rooted representative.
--
-- This removes a false terminal seam between the finite quotient L2 lane and
-- the wavefunction/operator lane. It does NOT promote Haar/Gibbs measure or a
-- physical Hamiltonian.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Base using (ℚ; 0ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanFiniteRootedGaugeQuotientL2Round197Exact as R197
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202

wavefunctionAsQuotientObservable :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  R202.BasedGaugeInvariantWavefunction group base →
  R197.QuotientObservable {group = group} {base = base} {paths = paths}
wavefunctionAsQuotientObservable wavefunction quotient =
  R202.evaluateOnRootedQuotient wavefunction quotient

finiteWavefunctionPairing :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  R197.FiniteRootedQuotientEnsemble group base paths →
  R202.BasedGaugeInvariantWavefunction group base →
  R202.BasedGaugeInvariantWavefunction group base →
  ℚ
finiteWavefunctionPairing ensemble left right =
  R197.finiteQuotientPairing ensemble
    (wavefunctionAsQuotientObservable left)
    (wavefunctionAsQuotientObservable right)

finiteWavefunctionNormSq :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  R197.FiniteRootedQuotientEnsemble group base paths →
  R202.BasedGaugeInvariantWavefunction group base →
  ℚ
finiteWavefunctionNormSq ensemble wavefunction =
  finiteWavefunctionPairing ensemble wavefunction wavefunction

finiteWavefunctionPairingSymmetric :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (ensemble : R197.FiniteRootedQuotientEnsemble group base paths)
    left right →
  finiteWavefunctionPairing ensemble left right
  ≡ finiteWavefunctionPairing ensemble right left
finiteWavefunctionPairingSymmetric ensemble left right =
  R197.finiteQuotientPairingSymmetric ensemble
    (wavefunctionAsQuotientObservable left)
    (wavefunctionAsQuotientObservable right)

finiteWavefunctionNormIsRootedNorm :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (ensemble : R197.FiniteRootedQuotientEnsemble group base paths)
    wavefunction →
  finiteWavefunctionNormSq ensemble wavefunction
  ≡ R197.finiteQuotientNormSq ensemble
      (wavefunctionAsQuotientObservable wavefunction)
finiteWavefunctionNormIsRootedNorm ensemble wavefunction = refl

finiteWavefunctionNormZeroOnRootedStates :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (ensemble : R197.FiniteRootedQuotientEnsemble group base paths)
    (wavefunction : R202.BasedGaugeInvariantWavefunction group base) →
  finiteWavefunctionNormSq ensemble wavefunction ≡ 0ℚ →
  ∀ quotient →
    R202.evaluateOnRootedQuotient wavefunction quotient ≡ 0ℚ
finiteWavefunctionNormZeroOnRootedStates ensemble wavefunction normZero =
  R197.finiteQuotientNormZeroPointwise ensemble
    (wavefunctionAsQuotientObservable wavefunction)
    normZero

-- Applying an R202 operator remains in the same finite L2 carrier because its
-- codomain is again a gauge-invariant wavefunction.
finiteOperatorOutputNormSq :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  R197.FiniteRootedQuotientEnsemble group base paths →
  R202.GaugeInvariantWavefunctionOperator group base →
  R202.BasedGaugeInvariantWavefunction group base →
  ℚ
finiteOperatorOutputNormSq ensemble operator wavefunction =
  finiteWavefunctionNormSq ensemble (R202.act operator wavefunction)

wavefunctionFiniteL2BridgeRound203Level : ProofLevel
wavefunctionFiniteL2BridgeRound203Level = machineChecked

wavefunctionFiniteL2DefinitenessRound203Level : ProofLevel
wavefunctionFiniteL2DefinitenessRound203Level = machineChecked

literalPhysicalGaugeInvariantL2MeasureRound203Level : ProofLevel
literalPhysicalGaugeInvariantL2MeasureRound203Level = conditional

literalFiniteYMHamiltonianRound203Level : ProofLevel
literalFiniteYMHamiltonianRound203Level = conditional
