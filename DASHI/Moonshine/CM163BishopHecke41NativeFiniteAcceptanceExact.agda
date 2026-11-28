module DASHI.Moonshine.CM163BishopHecke41NativeFiniteAcceptanceExact where

-- LOCAL ACCEPTANCE ENTRYPOINT, SOURCE-WRITTEN, UNEXECUTED.
-- Force the three actual finite residual decisions here, not in the
-- analytic import chain. If the pinned kernel cannot normalize them,
-- improve the executable checker; do not replace a gate with a receipt.
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Relation.Nullary.Decidable.Core using (from-yes)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact as Cert
import DASHI.Moonshine.CM163BishopHecke41PacketPrefixWeldExact as W
import DASHI.Moonshine.CM163BishopHecke41LiteralResidualReflectionExact as R
import DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact as O
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11

module At (inputs : Round11.BishopCutset) where
  module B = W.At inputs
  module F = R.At inputs
  module Actual = O.At inputs

  unitChecked : B.UnitGate
  unitChecked = from-yes Cert.unitCheck

  diagonalChecked : B.DiagonalGate
  diagonalChecked = from-yes Cert.diagCheck

  sliceChecked : B.SliceGate
  sliceChecked = from-yes Cert.sliceCheck

  diagonalResidualZero : ∀ n → n ≤ 3362 → C._≈C_ (Actual.diagonalResidual n) A.zeroC
  diagonalResidualZero = F.diagonalZero unitChecked diagonalChecked

  sliceResidualZero : ∀ n → n ≤ 1722 → C._≈C_ (Actual.sliceResidual n) A.zeroC
  sliceResidualZero = F.sliceZero unitChecked sliceChecked
