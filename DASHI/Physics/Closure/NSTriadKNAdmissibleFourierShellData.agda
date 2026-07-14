module DASHI.Physics.Closure.NSTriadKNAdmissibleFourierShellData where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (ℤ)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar

------------------------------------------------------------------------
-- Symbolic Fourier state for an exact finite shell.
--
-- This deliberately quantifies over arbitrary admissible data.  It does not
-- read a telemetry archive and it does not pick amplitudes or phases from one
-- simulation.  The complex interface is kept minimal: the present Gram-order
-- theorem needs reality, divergence-freedom, and a scalar norm realization,
-- but not a completed complex-analysis library.
------------------------------------------------------------------------

record ComplexFourierInterface (S : Scalar.ExactOrderedScalar) : Set₁ where
  field
    Complex : Set
    zeroComplex : Complex
    _+ᶜ_ : Complex → Complex → Complex
    integerScale : ℤ → Complex → Complex
    conjugate : Complex → Complex

    FourierVector : Set
    component₁ component₂ component₃ : FourierVector → Complex
    conjugateVector : FourierVector → FourierVector
    coefficientNormSq : FourierVector → Scalar.Scalar S

    conjugateVectorComponent₁ :
      (v : FourierVector) → component₁ (conjugateVector v) ≡ conjugate (component₁ v)
    conjugateVectorComponent₂ :
      (v : FourierVector) → component₂ (conjugateVector v) ≡ conjugate (component₂ v)
    conjugateVectorComponent₃ :
      (v : FourierVector) → component₃ (conjugateVector v) ≡ conjugate (component₃ v)

open ComplexFourierInterface public

dotModeCoefficient :
  {S : Scalar.ExactOrderedScalar} →
  (C : ComplexFourierInterface S) → Lattice.LatticeMode3 → FourierVector C → Complex C
dotModeCoefficient C k v =
  _+ᶜ_ C (integerScale C (Lattice.k₁ k) (component₁ C v))
    (_+ᶜ_ C (integerScale C (Lattice.k₂ k) (component₂ C v))
      (integerScale C (Lattice.k₃ k) (component₃ C v)))

-- This is the exact interaction formula boundary.  A later NS nonlinearity
-- module must inhabit it from the Fourier bilinear form; keeping it separate
-- prevents an arbitrary coherence function from being treated as physical.
record PhysicalTriadInteractionLaw
    (S : Scalar.ExactOrderedScalar)
    (C : ComplexFourierInterface S)
    (N : Nat) : Set₁ where
  field
    coherenceFormula :
      (Lattice.LatticeMode3 → FourierVector C) →
      Lattice.LatticeTriad → Scalar.Scalar S

open PhysicalTriadInteractionLaw public

record AdmissibleFourierShellData
    (S : Scalar.ExactOrderedScalar)
    (C : ComplexFourierInterface S)
    (N : Nat)
    (interaction : PhysicalTriadInteractionLaw S C N) : Set₁ where
  field
    coefficient : Lattice.LatticeMode3 → FourierVector C

    reality :
      (k : Lattice.LatticeMode3) →
      coefficient (Lattice.modeNeg k) ≡ conjugateVector C (coefficient k)
    divergenceFree :
      (k : Lattice.LatticeMode3) →
      dotModeCoefficient C k (coefficient k) ≡ zeroComplex C

    amplitude : Lattice.LatticeMode3 → Scalar.Scalar S
    amplitudeNonnegative :
      (k : Lattice.LatticeMode3) → Scalar.Nonnegative S (amplitude k)
    amplitudeRealizesCoefficientNorm :
      (k : Lattice.LatticeMode3) →
      Scalar._*_ S (amplitude k) (amplitude k) ≡
      coefficientNormSq C (coefficient k)

    coherence : Lattice.LatticeTriad → Scalar.Scalar S
    coherenceRealization :
      (τ : Lattice.LatticeTriad) →
      coherence τ ≡ coherenceFormula interaction coefficient τ
    coherenceWithinMinusOneOne :
      (τ : Lattice.LatticeTriad) → Scalar.WithinMinusOneOne S (coherence τ)

open AdmissibleFourierShellData public

triadAmplitudeFactor :
  {S : Scalar.ExactOrderedScalar} → {C : ComplexFourierInterface S} →
  {N : Nat} → {interaction : PhysicalTriadInteractionLaw S C N} →
  AdmissibleFourierShellData S C N interaction →
  Lattice.LatticeTriad → Scalar.Scalar S
triadAmplitudeFactor {S = S} u τ =
  Scalar.third S
    (Scalar._*_ S (amplitude u (Lattice.left τ))
      (Scalar._*_ S (amplitude u (Lattice.right τ))
        (amplitude u (Lattice.out τ))))

triadAbsoluteCoefficient :
  {S : Scalar.ExactOrderedScalar} → {C : ComplexFourierInterface S} →
  {N : Nat} → {interaction : PhysicalTriadInteractionLaw S C N} →
  AdmissibleFourierShellData S C N interaction →
  Lattice.LatticeTriad → Scalar.Scalar S
triadAbsoluteCoefficient {S = S} u τ =
  Scalar._*_ S (triadAmplitudeFactor u τ) (Scalar.abs S (coherence u τ))

triadNegativeCoefficient :
  {S : Scalar.ExactOrderedScalar} → {C : ComplexFourierInterface S} →
  {N : Nat} → {interaction : PhysicalTriadInteractionLaw S C N} →
  AdmissibleFourierShellData S C N interaction →
  Lattice.LatticeTriad → Scalar.Scalar S
triadNegativeCoefficient {S = S} u τ =
  Scalar._*_ S (triadAmplitudeFactor u τ) (Scalar.maxNegative S (coherence u τ))

amplitudeFactorNonnegative :
  {S : Scalar.ExactOrderedScalar} → {C : ComplexFourierInterface S} →
  {N : Nat} → {interaction : PhysicalTriadInteractionLaw S C N} →
  (u : AdmissibleFourierShellData S C N interaction) →
  (τ : Lattice.LatticeTriad) → Scalar.Nonnegative S (triadAmplitudeFactor u τ)
amplitudeFactorNonnegative {S = S} u τ =
  Scalar.thirdPreservesNonnegative S
    (Scalar.multiplicationPreservesNonnegative S
      (amplitudeNonnegative u (Lattice.left τ))
      (Scalar.multiplicationPreservesNonnegative S
        (amplitudeNonnegative u (Lattice.right τ))
        (amplitudeNonnegative u (Lattice.out τ))))

negativeTriadCoefficientNonnegative :
  {S : Scalar.ExactOrderedScalar} → {C : ComplexFourierInterface S} →
  {N : Nat} → {interaction : PhysicalTriadInteractionLaw S C N} →
  (u : AdmissibleFourierShellData S C N interaction) →
  (τ : Lattice.LatticeTriad) →
  Scalar.Nonnegative S (triadNegativeCoefficient u τ)
negativeTriadCoefficientNonnegative {S = S} u τ =
  Scalar.multiplicationPreservesNonnegative S
    (amplitudeFactorNonnegative u τ)
    (Scalar.maxNegativeNonnegative S (coherence u τ))

negativeTriadCoefficientLeAbsolute :
  {S : Scalar.ExactOrderedScalar} → {C : ComplexFourierInterface S} →
  {N : Agda.Builtin.Nat.Nat} → {interaction : PhysicalTriadInteractionLaw S C N} →
  (u : AdmissibleFourierShellData S C N interaction) →
  (τ : Lattice.LatticeTriad) →
  Scalar._≤_ S (triadNegativeCoefficient u τ) (triadAbsoluteCoefficient u τ)
negativeTriadCoefficientLeAbsolute {S = S} u τ =
  Scalar.multiplicationMonotoneNonnegativeRight S
    (amplitudeFactorNonnegative u τ)
    (Scalar.maxNegativeLeAbs S (coherence u τ))
