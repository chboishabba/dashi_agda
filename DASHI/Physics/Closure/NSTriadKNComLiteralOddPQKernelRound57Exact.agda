module DASHI.Physics.Closure.NSTriadKNComLiteralOddPQKernelRound57Exact where

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
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- ROUND 57 CONTRIBUTION
--
-- Construct the literal odd P/Q kernel instead of postulating a scalar Gram
-- cell.  P is the repository's physical hard low projector at a selected
-- cutoff and Q is its Boolean complement.  For a physical transport matrix
-- entry T(input,output), the commutator entry is therefore exactly
--
--   +T  when output is P and input is Q   (PTQ),
--   -T  when output is Q and input is P   (-QTP),
--    0  on the two diagonal grade blocks.
--
-- Restricting this entry formula to a resonant physical triad and then to
-- `physicalOutputFiber` gives the literal finite same-output collision kernel
-- requested by the Com Schur lane.  The remaining analytic work is no longer
-- kernel construction: it is common-hat identification and post-cancellation
-- absolute fibre-mass bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportMatrixSkewRound40Exact as Matrix
import DASHI.Physics.Closure.NSTriadKNComLiteralOutputFibreKernelRound57Exact as Fibre

literalPTQEntryCoefficient :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (cutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output} →
  Matrix.PhysicalTransportMatrixEntry input output →
  C3.Complex (LP.realField model)
literalPTQEntryCoefficient model cutoff E velocity {input} {output} entry
  with LP.lowSelect model cutoff output | LP.lowSelect model cutoff input
... | true  | false = Matrix.transportEntryCoefficient E velocity entry
... | true  | true  = C3.complexZero (LP.realField model)
... | false | true  = C3.complexZero (LP.realField model)
... | false | false = C3.complexZero (LP.realField model)

literalQTPEntryCoefficient :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (cutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output} →
  Matrix.PhysicalTransportMatrixEntry input output →
  C3.Complex (LP.realField model)
literalQTPEntryCoefficient model cutoff E velocity {input} {output} entry
  with LP.lowSelect model cutoff output | LP.lowSelect model cutoff input
... | true  | false = C3.complexZero (LP.realField model)
... | true  | true  = C3.complexZero (LP.realField model)
... | false | true  = Matrix.transportEntryCoefficient E velocity entry
... | false | false = C3.complexZero (LP.realField model)

literalOddPQEntryCoefficient :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (cutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output} →
  Matrix.PhysicalTransportMatrixEntry input output →
  C3.Complex (LP.realField model)
literalOddPQEntryCoefficient model cutoff E velocity {input} {output} entry
  with LP.lowSelect model cutoff output | LP.lowSelect model cutoff input
... | true  | false = Matrix.transportEntryCoefficient E velocity entry
... | true  | true  = C3.complexZero (LP.realField model)
... | false | true  =
      C3.complexNegate (Matrix.transportEntryCoefficient E velocity entry)
... | false | false = C3.complexZero (LP.realField model)

literalOddPQEntryIsPTQMinusQTP :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (cutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output}
    (entry : Matrix.PhysicalTransportMatrixEntry input output) →
  literalOddPQEntryCoefficient model cutoff E velocity entry
  ≡ C3.complexSubtract
      (literalPTQEntryCoefficient model cutoff E velocity entry)
      (literalQTPEntryCoefficient model cutoff E velocity entry)
literalOddPQEntryIsPTQMinusQTP model cutoff E velocity {input} {output} entry
  with LP.lowSelect model cutoff output | LP.lowSelect model cutoff input
... | true  | false = refl
... | true  | true  = refl
... | false | true  = refl
... | false | false = refl

literalOddPQTriadCoefficient :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  Triad.PhysicalTriadIncidence → C3.Complex (LP.realField model)
literalOddPQTriadCoefficient model projectorCutoff E velocity tau =
  literalOddPQEntryCoefficient model projectorCutoff E velocity
    (Fibre.triadTransportEntry tau)

oddPQActive :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  Nat → Z3.FourierMode → Z3.FourierMode → Bool
oddPQActive model cutoff input output
  with LP.lowSelect model cutoff output | LP.lowSelect model cutoff input
... | true  | false = true
... | true  | true  = false
... | false | true  = true
... | false | false = false

literalOddPQDiagonalLowBlockVanishes :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (cutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output}
    (entry : Matrix.PhysicalTransportMatrixEntry input output) →
  LP.lowSelect model cutoff output ≡ true →
  LP.lowSelect model cutoff input ≡ true →
  literalOddPQEntryCoefficient model cutoff E velocity entry
  ≡ C3.complexZero (LP.realField model)
literalOddPQDiagonalLowBlockVanishes model cutoff E velocity {input} {output} entry outLow inLow
  rewrite outLow | inLow = refl

literalOddPQDiagonalHighBlockVanishes :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (cutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output}
    (entry : Matrix.PhysicalTransportMatrixEntry input output) →
  LP.lowSelect model cutoff output ≡ false →
  LP.lowSelect model cutoff input ≡ false →
  literalOddPQEntryCoefficient model cutoff E velocity entry
  ≡ C3.complexZero (LP.realField model)
literalOddPQDiagonalHighBlockVanishes model cutoff E velocity {input} {output} entry outHigh inHigh
  rewrite outHigh | inHigh = refl

literalOddPQKernelConstructedFromPhysicalTransportAndHardProjector : Bool
literalOddPQKernelConstructedFromPhysicalTransportAndHardProjector = true

physicalOddPQCommonHatSupportConstructed : Bool
physicalOddPQCommonHatSupportConstructed = false

physicalOddPQAbsoluteFibreMassBoundsConstructed : Bool
physicalOddPQAbsoluteFibreMassBoundsConstructed = false

literalOddPQKernelConstructedFromPhysicalTransportAndHardProjectorIsTrue :
  literalOddPQKernelConstructedFromPhysicalTransportAndHardProjector ≡ true
literalOddPQKernelConstructedFromPhysicalTransportAndHardProjectorIsTrue = refl
