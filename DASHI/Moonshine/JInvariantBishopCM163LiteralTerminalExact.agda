module DASHI.Moonshine.JInvariantBishopCM163LiteralTerminalExact where

-- SOURCE-WRITTEN. Native terminal composition: arithmetic inputs
-- are discharged internally; the original analytic CM cut is explicit.
open import Agda.Builtin.Nat using (Nat)
import Real as R
open R using (ℝ; _≃_; _⋆; ∣_∣)
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as J
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as L
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import DASHI.Moonshine.JInvariantBishopCM163HalfUnitIsolationExact as Iso
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Guard
import DASHI.Moonshine.JInvariantBishopCM163DiskCrossCoefficientExact as Jet
import DASHI.Moonshine.JInvariantBishopCM163HyperMajorantsExact as H
import DASHI.Foundations.BishopChudnovskyRawCoordinateWeldExact as Raw

record OriginalCMCut : Set where
  field
    enclosure : ∣ Iso.offset ∣ R.≤ Iso.half
    diagonalZero : L.descending Guard.Root.j R.0ℝ Packet.diagonal ≃ R.0ℝ
    a b : ℝ
    first : J.FirstQJet a
    second : J.SecondQJet b
    cross : Jet.literalResidual (Jet.A J.p a) (Jet.diskB J.p a b)
      (L.s2 ⋆) (L.s3 ⋆) (L.p2 ⋆) (L.p3 ⋆) ≃ R.0ℝ

module AtOriginalCM (c : OriginalCMCut) where
  open OriginalCMCut c
  root : J.CMRoot
  root = L.rootFromLiteralDiagonal enclosure diagonalZero

  signed : J.SignedJet
  signed = L.signedJetFromActualFirst a b first second cross

  module Actual = H.AtRoot root

  allRaw : (k : Nat) → Raw.RawCross k
  allRaw = Actual.rawFromCM signed


-- The original quotient's first and second coefficient jets are now
-- constructed internally from its actual evaluated E4/E6 jets, rather
-- than being supplied as arbitrary numbers satisfying the scalar equations.
import DASHI.Moonshine.JInvariantBishopCM163QuotientJetExact as QJ
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as Period

OriginalRayResidual : Set
OriginalRayResidual =
  Jet.literalResidual (Jet.A J.p QJ.a) (Jet.diskB J.p QJ.a QJ.b)
    (L.s2 ⋆) (L.s3 ⋆) (L.p2 ⋆) (L.p3 ⋆) ≃ R.0ℝ

cutFromOriginalQuotient :
  ∣ Iso.offset ∣ R.≤ Iso.half →
  L.descending Guard.Root.j R.0ℝ Packet.diagonal ≃ R.0ℝ →
  OriginalRayResidual → OriginalCMCut
cutFromOriginalQuotient enclosure diagonal cross =
  let root = L.rootFromLiteralDiagonal enclosure diagonal in
  record
    { enclosure = enclosure
    ; diagonalZero = diagonal
    ; a = QJ.a
    ; b = QJ.b
    ; first = QJ.first root
    ; second = QJ.second root
    ; cross = cross
    }

allRawFromOriginalQuotient :
  ∣ Iso.offset ∣ R.≤ Iso.half →
  L.descending Guard.Root.j R.0ℝ Packet.diagonal ≃ R.0ℝ →
  OriginalRayResidual → (k : Nat) → Raw.RawCross k
allRawFromOriginalQuotient enclosure diagonal cross =
  AtOriginalCM.allRaw (cutFromOriginalQuotient enclosure diagonal cross)

periodFromOriginalQuotient :
  ∣ Iso.offset ∣ R.≤ Iso.half →
  L.descending Guard.Root.j R.0ℝ Packet.diagonal ≃ R.0ℝ →
  OriginalRayResidual → Period.NativePeriod
periodFromOriginalQuotient enclosure diagonal cross =
  Raw.periodFromRaw (allRawFromOriginalQuotient enclosure diagonal cross)
