{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteMeasureWavefunctionL2BridgeRound205Exact where

------------------------------------------------------------------------
-- ROUND205 BIDI X-POLLINATION: LITERAL FINITE-MEASURE EXPECTATION -> THE
-- CORRECT GAUGE-INVARIANT WAVEFUNCTION PRE-HILBERT SURFACE.
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

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202

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

    -- Correct null-space semantics.  Pre-Hilbert definiteness is obtained only
    -- after quotienting by this relation, not by claiming pointwise equality.
    NullEquivalent :
      R202.BasedGaugeInvariantWavefunction group base →
      R202.BasedGaugeInvariantWavefunction group base → Set

    zeroSquareIffNullEquivalent : ∀ wavefunction →
      expectation selectedMeasure
        (pointwiseMul wavefunction wavefunction) ≡ 0ℚ
      → NullEquivalent wavefunction wavefunction

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

finiteMeasureWavefunctionNormZeroGivesNull :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    (semantics : FiniteMeasureWavefunctionSemantics group base Measure)
    wavefunction →
  finiteMeasureWavefunctionNormSq semantics wavefunction ≡ 0ℚ →
  NullEquivalent semantics wavefunction wavefunction
finiteMeasureWavefunctionNormZeroGivesNull semantics wavefunction =
  zeroSquareIffNullEquivalent semantics wavefunction

finiteMeasureWavefunctionL2BridgeRound205Level : ProofLevel
finiteMeasureWavefunctionL2BridgeRound205Level = machineChecked

-- Same-object physical seam: instantiate this semantics with the literal
-- finiteMeasure already welded to the selected Balaban density.  The measure
-- itself must not be replaced by a parallel counting/sample object.
literalBalabanFiniteMeasureExpectationSemanticsRound205Level : ProofLevel
literalBalabanFiniteMeasureExpectationSemanticsRound205Level = conditional

-- Completion and self-adjoint Hamiltonian still require the actual null quotient,
-- norm completion/domain and operator theory on that same measure.
literalBalabanFiniteMeasureL2CompletionRound205Level : ProofLevel
literalBalabanFiniteMeasureL2CompletionRound205Level = conditional
