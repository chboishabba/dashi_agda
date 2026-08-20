module DASHI.Physics.Closure.NSTriadKNComLiteralCrossGramFalsifierRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Historical 1955 conference source; no DOI assigned.
--
-- ROUND 62 CONCRETE-B CONTRIBUTION
--
-- Do the falsification-first calculation on the literal odd-(P/Q) output
-- fibre instead of introducing another abstract pair-product field.
--
-- For two projector cutoffs q,r and ONE actual physical output fibre F_k,
-- define directly in the exact `realField model`
--
--   <c_q,c_r>_F = sum_{tau in F_k} conjugate(c_q(tau)) c_r(tau),
--
--   G(q,r;k) = |<c_q,c_r>_F|^2,
--
-- together with the two literal fibre masses.  These are executable finite
-- folds over `physicalOutputFiber`; no rational or Bishop-real carrier is
-- substituted for the Fourier field.
--
-- A normalization witness may then supply the inverse of
--
--   mass_q(k) mass_r(k),
--
-- and the normalized diagnostic is definitionally
--
--   P(q,r;k) = G(q,r;k) * normalizationInverse.
--
-- This file deliberately does NOT identify one output-fibre diagnostic with
-- the global T_q^*T_r / T_qT_r^* operator norm.  Its purpose is the requested
-- concrete falsifier: before attempting a universal B theorem, instantiate a
-- nontrivial literal fibre and test the actual same/adjacent values against
-- the embedded 17/64 and 65/512 targets.  A failed fibre already rejects any
-- stronger theorem whose global quantity dominates this diagnostic.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQKernelRound57Exact as Odd
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as Ordered

------------------------------------------------------------------------
-- Literal cross-pairing and squared Gram numerator.
------------------------------------------------------------------------

crossPairingOver :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (leftCutoff rightCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  List Triad.PhysicalTriadIncidence →
  C3.Complex (LP.realField model)
crossPairingOver model leftCutoff rightCutoff E velocity [] =
  C3.complexZero (LP.realField model)
crossPairingOver model leftCutoff rightCutoff E velocity (tau ∷ rest) =
  C3.complexAdd
    (C3.complexMultiply
      (C3.complexConjugate
        (Odd.literalOddPQTriadCoefficient
          model leftCutoff E velocity tau))
      (Odd.literalOddPQTriadCoefficient
        model rightCutoff E velocity tau))
    (crossPairingOver model leftCutoff rightCutoff E velocity rest)

literalOutputFibreCrossPairing :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (leftCutoff rightCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  C3.Complex (LP.realField model)
literalOutputFibreCrossPairing
    model leftCutoff rightCutoff enumerationCutoff E velocity output =
  crossPairingOver model leftCutoff rightCutoff E velocity
    (Output.physicalOutputFiber enumerationCutoff output)

literalOutputFibreCrossGramNumerator :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (leftCutoff rightCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  C3.Carrier (LP.realField model)
literalOutputFibreCrossGramNumerator
    model leftCutoff rightCutoff enumerationCutoff E velocity output =
  Ordered.complexModulusSquared
    (literalOutputFibreCrossPairing
      model leftCutoff rightCutoff enumerationCutoff E velocity output)

------------------------------------------------------------------------
-- Literal one-side fibre mass.  This is the finite sum of |c|^2 on the same
-- output incidence list, not a separately supplied norm receipt.
------------------------------------------------------------------------

fibreMassOver :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  List Triad.PhysicalTriadIncidence →
  C3.Carrier (LP.realField model)
fibreMassOver model projectorCutoff E velocity [] =
  C3.zero (LP.realField model)
fibreMassOver model projectorCutoff E velocity (tau ∷ rest) =
  C3.add (LP.realField model)
    (Ordered.complexModulusSquared
      (Odd.literalOddPQTriadCoefficient
        model projectorCutoff E velocity tau))
    (fibreMassOver model projectorCutoff E velocity rest)

literalOutputFibreMass :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  C3.Carrier (LP.realField model)
literalOutputFibreMass
    model projectorCutoff enumerationCutoff E velocity output =
  fibreMassOver model projectorCutoff E velocity
    (Output.physicalOutputFiber enumerationCutoff output)

complexModulusSquaredNonnegative :
  ∀ {r}
    {F : C3.RealField r}
    (O : Ordered.OrderedRealExtension F)
    (value : C3.Complex F) →
  Ordered._≤_ O (C3.zero F) (Ordered.complexModulusSquared value)
complexModulusSquaredNonnegative {F = F} O value =
  Ordered.zeroBelowAdd O
    (Ordered.zeroBelowSquare O (C3.real value))
    (Ordered.zeroBelowSquare O (C3.imaginary value))

fibreMassOverNonnegative :
  ∀ {r}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    (O : Ordered.OrderedRealExtension (LP.realField model))
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (items : List Triad.PhysicalTriadIncidence) →
  Ordered._≤_ O
    (C3.zero (LP.realField model))
    (fibreMassOver model projectorCutoff E velocity items)
fibreMassOverNonnegative O projectorCutoff E velocity [] =
  Ordered.leqReflexive O _
fibreMassOverNonnegative {model = model} O projectorCutoff E velocity
    (tau ∷ rest) =
  Ordered.zeroBelowAdd O
    (complexModulusSquaredNonnegative O
      (Odd.literalOddPQTriadCoefficient
        model projectorCutoff E velocity tau))
    (fibreMassOverNonnegative O projectorCutoff E velocity rest)

literalOutputFibreMassNonnegative :
  ∀ {r}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    (O : Ordered.OrderedRealExtension (LP.realField model))
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  Ordered._≤_ O
    (C3.zero (LP.realField model))
    (literalOutputFibreMass
      model projectorCutoff enumerationCutoff E velocity output)
literalOutputFibreMassNonnegative O projectorCutoff enumerationCutoff E velocity output =
  fibreMassOverNonnegative O projectorCutoff E velocity
    (Output.physicalOutputFiber enumerationCutoff output)

literalCrossGramNumeratorNonnegative :
  ∀ {r}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    (O : Ordered.OrderedRealExtension (LP.realField model))
    (leftCutoff rightCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  Ordered._≤_ O
    (C3.zero (LP.realField model))
    (literalOutputFibreCrossGramNumerator
      model leftCutoff rightCutoff enumerationCutoff E velocity output)
literalCrossGramNumeratorNonnegative
    {model = model} O leftCutoff rightCutoff enumerationCutoff
    E velocity output =
  complexModulusSquaredNonnegative O
    (literalOutputFibreCrossPairing
      model leftCutoff rightCutoff enumerationCutoff E velocity output)

------------------------------------------------------------------------
-- Ordered multiplication is intentionally separated from the weaker ordered
-- additive carrier.  The literal Fourier field must provide this law if it is
-- to support normalized energy estimates.
------------------------------------------------------------------------

record NonnegativeProductLaw
    {r : Level}
    {F : C3.RealField r}
    (O : Ordered.OrderedRealExtension F) : Set (lsuc r) where
  field
    productNonnegative : ∀ {left right} →
      Ordered._≤_ O (C3.zero F) left →
      Ordered._≤_ O (C3.zero F) right →
      Ordered._≤_ O (C3.zero F) (C3.multiply F left right)

open NonnegativeProductLaw public

record LiteralOutputFibreNormalization
    {r : Level}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (O : Ordered.OrderedRealExtension (LP.realField model))
    (productLaw : NonnegativeProductLaw O)
    (leftCutoff rightCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) : Set (lsuc r) where
  field
    normalizationInverse : C3.Carrier (LP.realField model)
    normalizationInverseNonnegative :
      Ordered._≤_ O (C3.zero (LP.realField model)) normalizationInverse

    inverseMeaning :
      C3.multiply (LP.realField model)
        (C3.multiply (LP.realField model)
          (literalOutputFibreMass
            model leftCutoff enumerationCutoff E velocity output)
          (literalOutputFibreMass
            model rightCutoff enumerationCutoff E velocity output))
        normalizationInverse
      ≡ C3.one (LP.realField model)

open LiteralOutputFibreNormalization public

normalizedLiteralOutputFibreCrossGram :
  ∀ {r model O productLaw leftCutoff rightCutoff enumerationCutoff E velocity output} →
  LiteralOutputFibreNormalization
    {r} model O productLaw
    leftCutoff rightCutoff enumerationCutoff E velocity output →
  C3.Carrier (LP.realField model)
normalizedLiteralOutputFibreCrossGram
    {model = model}
    {leftCutoff = leftCutoff}
    {rightCutoff = rightCutoff}
    {enumerationCutoff = enumerationCutoff}
    {E = E} {velocity = velocity} {output = output}
    normalization =
  C3.multiply (LP.realField model)
    (literalOutputFibreCrossGramNumerator
      model leftCutoff rightCutoff enumerationCutoff E velocity output)
    (normalizationInverse normalization)

normalizedLiteralOutputFibreCrossGramNonnegative :
  ∀ {r model O productLaw leftCutoff rightCutoff enumerationCutoff E velocity output}
    (normalization : LiteralOutputFibreNormalization
      {r} model O productLaw
      leftCutoff rightCutoff enumerationCutoff E velocity output) →
  Ordered._≤_ O
    (C3.zero (LP.realField model))
    (normalizedLiteralOutputFibreCrossGram normalization)
normalizedLiteralOutputFibreCrossGramNonnegative
    {O = O} {productLaw = productLaw}
    {leftCutoff = leftCutoff} {rightCutoff = rightCutoff}
    {enumerationCutoff = enumerationCutoff}
    {E = E} {velocity = velocity} {output = output}
    normalization =
  productNonnegative productLaw
    (literalCrossGramNumeratorNonnegative O
      leftCutoff rightCutoff enumerationCutoff E velocity output)
    (normalizationInverseNonnegative normalization)

------------------------------------------------------------------------
-- Exact diagnostic record.  This is what the next finite calculation should
-- instantiate before any universal B wrapper is attempted.
------------------------------------------------------------------------

record ConcreteLiteralOddPQFibreDiagnostic
    {r : Level}
    (model : LP.PeriodicHardShellFourierPDE {r}) : Set (lsuc r) where
  field
    ordered : Ordered.OrderedRealExtension (LP.realField model)
    productLaw : NonnegativeProductLaw ordered
    integerEmbedding : C3.IntegerEmbedding (LP.realField model)
    velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)
    enumerationCutoff leftCutoff rightCutoff : Nat
    output : Z3.FourierMode

    normalization : LiteralOutputFibreNormalization
      model ordered productLaw
      leftCutoff rightCutoff enumerationCutoff integerEmbedding velocity output

open ConcreteLiteralOddPQFibreDiagnostic public

diagnosticValue :
  ∀ {r model} →
  ConcreteLiteralOddPQFibreDiagnostic {r} model →
  C3.Carrier (LP.realField model)
diagnosticValue diagnostic =
  normalizedLiteralOutputFibreCrossGram (normalization diagnostic)

literalOddPQCrossGramNumeratorConstructed : Bool
literalOddPQCrossGramNumeratorConstructed = true

literalOddPQFibreMassConstructed : Bool
literalOddPQFibreMassConstructed = true

literalOddPQNormalizedFibreDiagnosticConstructed : Bool
literalOddPQNormalizedFibreDiagnosticConstructed = true

literalOddPQCrossGramNumeratorConstructedIsTrue :
  literalOddPQCrossGramNumeratorConstructed ≡ true
literalOddPQCrossGramNumeratorConstructedIsTrue = refl

literalOddPQFibreMassConstructedIsTrue :
  literalOddPQFibreMassConstructed ≡ true
literalOddPQFibreMassConstructedIsTrue = refl

literalOddPQNormalizedFibreDiagnosticConstructedIsTrue :
  literalOddPQNormalizedFibreDiagnosticConstructed ≡ true
literalOddPQNormalizedFibreDiagnosticConstructedIsTrue = refl
