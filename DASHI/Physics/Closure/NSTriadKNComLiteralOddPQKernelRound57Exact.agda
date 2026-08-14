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
-- cell. P is the repository's physical hard low projector at a selected
-- cutoff and Q is its Boolean complement. For a physical transport entry T,
-- the commutator coefficient is exactly +T on PTQ, -T on QTP, and zero on the
-- two diagonal grade blocks.  The coefficient is then mapped over the ACTUAL
-- finite `physicalOutputFiber`, so the same-output collision list now exists as
-- a literal object before any absolute-value/Schur majorisation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; map)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
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

literalOddPQTriadCoefficient :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  Triad.PhysicalTriadIncidence → C3.Complex (LP.realField model)
literalOddPQTriadCoefficient model projectorCutoff E velocity tau =
  literalOddPQEntryCoefficient model projectorCutoff E velocity
    (Fibre.triadTransportEntry tau)

literalOddPQOutputFibreCoefficients :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  List (C3.Complex (LP.realField model))
literalOddPQOutputFibreCoefficients model projectorCutoff enumerationCutoff E velocity output =
  map
    (literalOddPQTriadCoefficient model projectorCutoff E velocity)
    (Output.physicalOutputFiber enumerationCutoff output)

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

literalOddPQSameOutputCollisionListConstructed : Bool
literalOddPQSameOutputCollisionListConstructed = true

physicalOddPQCommonHatSupportConstructed : Bool
physicalOddPQCommonHatSupportConstructed = false

physicalOddPQAbsoluteFibreMassBoundsConstructed : Bool
physicalOddPQAbsoluteFibreMassBoundsConstructed = false

literalOddPQKernelConstructedFromPhysicalTransportAndHardProjectorIsTrue :
  literalOddPQKernelConstructedFromPhysicalTransportAndHardProjector ≡ true
literalOddPQKernelConstructedFromPhysicalTransportAndHardProjectorIsTrue = refl

literalOddPQSameOutputCollisionListConstructedIsTrue :
  literalOddPQSameOutputCollisionListConstructed ≡ true
literalOddPQSameOutputCollisionListConstructedIsTrue = refl
