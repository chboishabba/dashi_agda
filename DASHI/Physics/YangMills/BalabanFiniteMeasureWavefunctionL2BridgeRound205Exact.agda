{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteMeasureWavefunctionL2BridgeRound205Exact where

------------------------------------------------------------------------
-- ROUND205 BIDI X-POLLINATION: LITERAL FINITE-MEASURE EXPECTATION -> THE
-- CORRECT GAUGE-INVARIANT WAVEFUNCTION QUOTIENT-PAIRING SURFACE.
--
-- R202 fixes the physical carrier: H acts on gauge-invariant wavefunctions,
-- not gauge configurations.  The older P5 finite-measure lane already records
-- finite measures and an expectation map, but its predicate `Positive measure`
-- is intentionally abstract; it does not definitionally say that expectation
-- of a square is nonnegative or identify the null space of that quadratic form.
--
-- This owner records the least additional semantics needed on the SAME finite
-- measure.  It does not construct a new Haar/Gibbs measure and does not turn a
-- generic positivity label into an inner-product theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202

zeroWavefunction :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N} →
  R202.BasedGaugeInvariantWavefunction group base
zeroWavefunction = record
  { R202.BasedGaugeInvariantWavefunction.amplitude = λ _ → 0ℚ
  ; R202.BasedGaugeInvariantWavefunction.invariantUnderBasedArrow =
      λ arrow based → refl
  }

record FiniteMeasureWavefunctionSemantics
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (Measure : Set) : Set₁ where
  field
    selectedMeasure : Measure

    expectation :
      Measure → R202.BasedGaugeInvariantWavefunction group base → ℚ

    pointwiseAdd pointwiseMul :
      R202.BasedGaugeInvariantWavefunction group base →
      R202.BasedGaugeInvariantWavefunction group base →
      R202.BasedGaugeInvariantWavefunction group base

    pointwiseAddAmplitude : ∀ left right field →
      R202.amplitude (pointwiseAdd left right) field
      ≡ R202.amplitude left field + R202.amplitude right field

    pointwiseMulAmplitude : ∀ left right field →
      R202.amplitude (pointwiseMul left right) field
      ≡ R202.amplitude left field * R202.amplitude right field

    expectationAdditive : ∀ left right →
      expectation selectedMeasure (pointwiseAdd left right)
      ≡ expectation selectedMeasure left + expectation selectedMeasure right

    squareExpectationNonnegative : ∀ wavefunction →
      0ℚ ≤ expectation selectedMeasure
        (pointwiseMul wavefunction wavefunction)

    -- Null-space semantics is an actual equivalence relation.  A zero norm must
    -- place the wavefunction in the equivalence class of the literal zero
    -- wavefunction; reflexivity alone would be vacuous.
    NullEquivalent :
      R202.BasedGaugeInvariantWavefunction group base →
      R202.BasedGaugeInvariantWavefunction group base → Set

    nullReflexive : ∀ wavefunction →
      NullEquivalent wavefunction wavefunction

    nullSymmetric : ∀ {left right} →
      NullEquivalent left right → NullEquivalent right left

    nullTransitive : ∀ {left middle right} →
      NullEquivalent left middle →
      NullEquivalent middle right →
      NullEquivalent left right

    zeroSquareImpliesNullEquivalentToZero : ∀ wavefunction →
      expectation selectedMeasure
        (pointwiseMul wavefunction wavefunction) ≡ 0ℚ
      → NullEquivalent wavefunction zeroWavefunction

    -- The pairing must itself descend through the null relation.  Without these
    -- laws one merely has an equivalence relation beside a pairing, not a
    -- quotient-defined pairing.
    pairingNullCongruentLeft : ∀ {left left'} →
      NullEquivalent left left' →
      ∀ right →
      expectation selectedMeasure (pointwiseMul left right)
      ≡ expectation selectedMeasure (pointwiseMul left' right)

    pairingNullCongruentRight : ∀ {right right'} →
      NullEquivalent right right' →
      ∀ left →
      expectation selectedMeasure (pointwiseMul left right)
      ≡ expectation selectedMeasure (pointwiseMul left right')

open FiniteMeasureWavefunctionSemantics public

finiteMeasureWavefunctionPairing :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set} →
  FiniteMeasureWavefunctionSemantics group base Measure →
  R202.BasedGaugeInvariantWavefunction group base →
  R202.BasedGaugeInvariantWavefunction group base → ℚ
finiteMeasureWavefunctionPairing semantics left right =
  expectation semantics (selectedMeasure semantics)
    (pointwiseMul semantics left right)

finiteMeasureWavefunctionPairingCongruentLeft :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    (semantics : FiniteMeasureWavefunctionSemantics group base Measure)
    {left left'} →
  NullEquivalent semantics left left' →
  ∀ right →
  finiteMeasureWavefunctionPairing semantics left right
  ≡ finiteMeasureWavefunctionPairing semantics left' right
finiteMeasureWavefunctionPairingCongruentLeft semantics =
  pairingNullCongruentLeft semantics

finiteMeasureWavefunctionPairingCongruentRight :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    (semantics : FiniteMeasureWavefunctionSemantics group base Measure)
    {right right'} →
  NullEquivalent semantics right right' →
  ∀ left →
  finiteMeasureWavefunctionPairing semantics left right
  ≡ finiteMeasureWavefunctionPairing semantics left right'
finiteMeasureWavefunctionPairingCongruentRight semantics =
  pairingNullCongruentRight semantics

finiteMeasureWavefunctionNormSq :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set} →
  FiniteMeasureWavefunctionSemantics group base Measure →
  R202.BasedGaugeInvariantWavefunction group base → ℚ
finiteMeasureWavefunctionNormSq semantics wavefunction =
  finiteMeasureWavefunctionPairing semantics wavefunction wavefunction

finiteMeasureWavefunctionNormNonnegative :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    (semantics : FiniteMeasureWavefunctionSemantics group base Measure)
    wavefunction →
  0ℚ ≤ finiteMeasureWavefunctionNormSq semantics wavefunction
finiteMeasureWavefunctionNormNonnegative semantics wavefunction =
  squareExpectationNonnegative semantics wavefunction

finiteMeasureWavefunctionNormZeroGivesNullToZero :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    (semantics : FiniteMeasureWavefunctionSemantics group base Measure)
    wavefunction →
  finiteMeasureWavefunctionNormSq semantics wavefunction ≡ 0ℚ →
  NullEquivalent semantics wavefunction zeroWavefunction
finiteMeasureWavefunctionNormZeroGivesNullToZero semantics wavefunction =
  zeroSquareImpliesNullEquivalentToZero semantics wavefunction

finiteMeasureWavefunctionL2BridgeRound205Level : ProofLevel
finiteMeasureWavefunctionL2BridgeRound205Level = machineChecked

finiteMeasureWavefunctionNullSemanticsRound205Level : ProofLevel
finiteMeasureWavefunctionNullSemanticsRound205Level = machineChecked

finiteMeasureWavefunctionQuotientPairingRound205Level : ProofLevel
finiteMeasureWavefunctionQuotientPairingRound205Level = machineChecked

-- Same-object physical seam: instantiate this semantics with the literal
-- finiteMeasure already welded to the selected Balaban density.  The measure
-- itself must not be replaced by a parallel counting/sample object.
literalBalabanFiniteMeasureExpectationSemanticsRound205Level : ProofLevel
literalBalabanFiniteMeasureExpectationSemanticsRound205Level = conditional

-- Completion and self-adjoint Hamiltonian still require the actual quotient by
-- NullEquivalent, its norm completion/domain and operator theory on that same
-- measure.
literalBalabanFiniteMeasureL2CompletionRound205Level : ProofLevel
literalBalabanFiniteMeasureL2CompletionRound205Level = conditional
