module DASHI.Moonshine.BishopRound11MachinEisensteinRouteBExact where

------------------------------------------------------------------------
-- ACTUAL AGDA SOURCE CAPSTONE FOR ROUTE B
--
-- For every selected Round11 Bishop cutset this module fixes:
--
--   * the actual Round11 configured trig power-series package;
--   * the machine-produced concrete signed-factorial identification;
--   * the actual Bishop Machin pi;
--   * the setoid-native complex carrier over vendored Bishop reals;
--   * the literal q, E4_N, E6_N and discriminant-numerator recurrences.
--
-- No legacy propositional quotient is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.BishopSetoidComplexExact as Complex
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Source
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidFiniteQSeriesExact as Q
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

transcendentals :
  Round11.Round11BishopCutset →
  Complex.BishopSetoidComplexTranscendentals
transcendentals =
  Source.round11MachinTranscendentals

qOf :
  Round11.Round11BishopCutset →
  Complex.BishopComplex →
  Complex.BishopComplex
qOf inputs =
  Q.qOf (transcendentals inputs)

e4Truncated :
  Round11.Round11BishopCutset →
  Q.DivisorPowerKernel →
  Nat →
  Complex.BishopComplex →
  Complex.BishopComplex
e4Truncated inputs =
  Q.e4Truncated (transcendentals inputs)

e6Truncated :
  Round11.Round11BishopCutset →
  Q.DivisorPowerKernel →
  Nat →
  Complex.BishopComplex →
  Complex.BishopComplex
e6Truncated inputs =
  Q.e6Truncated (transcendentals inputs)

discriminantNumeratorTruncated :
  Round11.Round11BishopCutset →
  Q.DivisorPowerKernel →
  Nat →
  Complex.BishopComplex →
  Complex.BishopComplex
discriminantNumeratorTruncated inputs =
  Q.discriminantNumeratorTruncated
    (transcendentals inputs)

qCongruent :
  (inputs : Round11.Round11BishopCutset) →
  ∀ {left right} →
  Complex._≈C_ left right →
  Complex._≈C_
    (qOf inputs left)
    (qOf inputs right)
qCongruent inputs =
  Q.qOfCongruent (transcendentals inputs)

e4Congruent :
  (inputs : Round11.Round11BishopCutset) →
  (kernel : Q.DivisorPowerKernel) →
  (terms : Nat) →
  ∀ {left right} →
  Complex._≈C_ left right →
  Complex._≈C_
    (e4Truncated inputs kernel terms left)
    (e4Truncated inputs kernel terms right)
e4Congruent inputs =
  Q.e4TruncatedCongruent (transcendentals inputs)

e6Congruent :
  (inputs : Round11.Round11BishopCutset) →
  (kernel : Q.DivisorPowerKernel) →
  (terms : Nat) →
  ∀ {left right} →
  Complex._≈C_ left right →
  Complex._≈C_
    (e6Truncated inputs kernel terms left)
    (e6Truncated inputs kernel terms right)
e6Congruent inputs =
  Q.e6TruncatedCongruent (transcendentals inputs)

discriminantNumeratorCongruent :
  (inputs : Round11.Round11BishopCutset) →
  (kernel : Q.DivisorPowerKernel) →
  (terms : Nat) →
  ∀ {left right} →
  Complex._≈C_ left right →
  Complex._≈C_
    (discriminantNumeratorTruncated
      inputs kernel terms left)
    (discriminantNumeratorTruncated
      inputs kernel terms right)
discriminantNumeratorCongruent inputs =
  Q.discriminantNumeratorTruncatedCongruent
    (transcendentals inputs)

record Round11MachinEisensteinSourceReceipt
    (inputs : Round11.Round11BishopCutset) : Set₁ where
  constructor round11-machin-eisenstein-source-receipt
  field
    sourceTranscendentals :
      Complex.BishopSetoidComplexTranscendentals

    sourceTranscendentalsExact :
      sourceTranscendentals ≡ transcendentals inputs

    q :
      Complex.BishopComplex →
      Complex.BishopComplex

    e4 :
      Q.DivisorPowerKernel →
      Nat →
      Complex.BishopComplex →
      Complex.BishopComplex

    e6 :
      Q.DivisorPowerKernel →
      Nat →
      Complex.BishopComplex →
      Complex.BishopComplex

    deltaNumerator :
      Q.DivisorPowerKernel →
      Nat →
      Complex.BishopComplex →
      Complex.BishopComplex

    qExact :
      q ≡ qOf inputs

    e4Exact :
      e4 ≡ e4Truncated inputs

    e6Exact :
      e6 ≡ e6Truncated inputs

    deltaNumeratorExact :
      deltaNumerator ≡
        discriminantNumeratorTruncated inputs

open Round11MachinEisensteinSourceReceipt public

canonicalRound11MachinEisensteinSourceReceipt :
  (inputs : Round11.Round11BishopCutset) →
  Round11MachinEisensteinSourceReceipt inputs
canonicalRound11MachinEisensteinSourceReceipt inputs =
  round11-machin-eisenstein-source-receipt
    (transcendentals inputs)
    refl
    (qOf inputs)
    (e4Truncated inputs)
    (e6Truncated inputs)
    (discriminantNumeratorTruncated inputs)
    refl refl refl refl

record Boundary : Set where
  constructor boundary
  field
    actualRound11TrigPackageSelected : Bool
    actualMachinPiSelected : Bool
    bishopSetoidComplexSelected : Bool
    literalQOwned : Bool
    literalE4Owned : Bool
    literalE6Owned : Bool
    literalDiscriminantNumeratorOwned : Bool
    allFiniteObjectsSetoidCongruent : Bool
    legacyPropositionalQuotientUsed : Bool

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    true true true true true true true true
    false
