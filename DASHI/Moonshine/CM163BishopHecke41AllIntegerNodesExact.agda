module DASHI.Moonshine.CM163BishopHecke41AllIntegerNodesExact where

-- PAPER 9 G1/G2 COARSE MAX-CUT, SOURCE-WRITTEN, KERNEL PENDING.
-- All 43 Y-node proofs come from the SAME original integer matrix and
-- SAME original unit certificate. No fitted matrix, node oracle, or
-- nonconstructive sampling/density principle is used here.
--
-- This module does NOT claim the residual is globally zero merely
-- because it vanishes to high order at the cusp. Each node still
-- requires the original holomorphic/rigidity argument (or another
-- valid global identity producer). Proof-relevant pole removal is all
-- that the finite reflection alone supplies.

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.Integer.Base as Z using (ℤ; +_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable.Core using (from-yes)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact as Cert
import DASHI.Moonshine.CM163Hecke41FullIntegerMatrixExact as Matrix
import DASHI.Moonshine.CM163BishopHecke41IntegerSpecializationReflectionExact as Reflect
import DASHI.Moonshine.CM163BishopHecke41NativeFiniteAcceptanceExact as Native
import DASHI.Moonshine.CM163BishopHecke41ArbitrarySliceSeriesExact as Series
import DASHI.Moonshine.CM163BishopHecke41ArbitrarySliceResidualExact as Residual
import DASHI.Moonshine.CM163BishopHecke41IntegerSpecializationExact as Special
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11

-- 0..42 suffices for degree <= 42. Signed -21..21 is an optional
-- independent control, not a prerequisite for polynomial uniqueness.
node : Nat → ℤ
node n = + n

candidate : Matrix.Coefficient
candidate = Matrix.originalMatrix

module At (inputs : Round11.BishopCutset) where
  module R = Reflect.At inputs
  module N = Native.At inputs
  module S = Special.At inputs

  module For (n : Nat) where
    module F = R.For candidate (node n)

    Gate : Set
    Gate = F.Gate

    gate? : Dec Gate
    gate? = F.gate?

    -- This is the actual arbitrary-target original ramified series,
    -- with its 43-column integer candidate specialized at node n.
    zeroPrefix : N.B.UnitGate → Gate → F.S.S.PrefixGate
    zeroPrefix hu hn = F.zeroPrefix hu hn

    poleRemoved : N.B.UnitGate → Gate → ∀ p →
      C._≈C_ (F.S.S.residual p)
        (A._*C_ (R.A0.A0.t p) (Eval.value (F.S.S.tail p)))
    poleRemoved hu hn = F.poleRemoved hu hn

  NodeGates : Set
  NodeGates = Cert.Through 42 (λ n → For.Gate n)

  nodes? : Dec NodeGates
  nodes? = Cert.decThrough 42 (λ n → For.Gate n) (λ n → For.gate? n)

  nodeAt : NodeGates → ∀ n → n ≤ 42 → For.Gate n
  nodeAt gates n bound = Cert.throughAt 42 gates n bound

  -- The two exact finite antecedents can be accepted independently.
  -- Running this requires reduction of the concrete arithmetic gates;
  -- from-yes is intentionally isolated to native acceptance.
  nativeUnit : N.B.UnitGate
  nativeUnit = N.unitChecked

  nodePole : NodeGates → ∀ n → n ≤ 42 → ∀ p →
    C._≈C_ (For.F.S.S.residual n p)
      (A._*C_ (R.A0.A0.t p) (Eval.value (For.F.S.S.tail n p)))
  nodePole gates n hn = For.poleRemoved n nativeUnit (nodeAt gates n hn)
