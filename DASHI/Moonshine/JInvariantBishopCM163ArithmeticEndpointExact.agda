module DASHI.Moonshine.JInvariantBishopCM163ArithmeticEndpointExact where

-- Source-written. The three Ramanujan inputs are constructed from the
-- original native divisor geometry; only the actual CM source identities
-- remain. The signed ray coefficients below are the unique scalar solution
-- of the original first and second q-jet equations.
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆)
import RealProperties as P
import Inverse as Inv
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as J
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Packet
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Literal
import DASHI.Moonshine.JInvariantBishopCM163HalfUnitIsolationExact as Iso
import DASHI.Moonshine.JInvariantBishopCM163DiskCrossCoefficientExact as Disk
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Guard
import DASHI.Moonshine.JInvariantBishopCM163HyperMajorantsExact as Major
import DASHI.Moonshine.JInvariantBishopRamanujanNativeExact as Ram
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N
import DASHI.Foundations.BishopChudnovskyRawCoordinateWeldExact as Raw
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as Period
import Data.Rational.Unnormalised as Q

ix : ℝ
ix = Packet.xInv

xCancels : (v : ℝ) → (J.X * (ix * v)) ≃ v
xCancels v = P.≃-trans (P.≃-symm (P.*-assoc J.X ix v))
  (P.≃-trans (P.*-congʳ (Inv.*-inverseʳ J.X Packet.xNZ)) (P.*-identityˡ v))

-- Reverse-solved scalar readouts of the actual CM jet equations.
-- These definitions do not by themselves establish the analytic derivative
-- interpretation; that interpretation is supplied by the original germ.
first : ℝ
first = ix * R.- (J.K * J.Y)

firstEquation : J.FirstQJet first
firstEquation = xCancels (R.- (J.K * J.Y))

secondNumerator : ℝ
secondNumerator = J.K * (J.three * N.cube J.X + J.three * N.sq J.Y - J.Y * J.U)

second : ℝ
second = ((+ 1 / 6) ⋆) * ix * ix * secondNumerator

secondEquation : J.SecondQJet second
secondEquation =
  P.≃-trans
    (let open P.ℝ-Solver in solve 3 (λ x i v →
      Κ (+ 6 / 1) ⊗ (x ⊗ x) ⊗ (Κ (+ 1 / 6) ⊗ i ⊗ i ⊗ v)
      ⊜ x ⊗ (i ⊗ (x ⊗ (i ⊗ v))))
      P.≃-refl J.X ix secondNumerator)
    (P.≃-trans (xCancels (J.X * (ix * secondNumerator))) (xCancels secondNumerator))

firstUnique : (a : ℝ) → J.FirstQJet a → a ≃ first
firstUnique a h = N.cancelLeft J.X Guard.xPositive (P.≃-trans h (P.≃-symm firstEquation))

secondUnique : (b : ℝ) → J.SecondQJet b → b ≃ second
secondUnique b h = N.cancelLeft (N.six * N.sq J.X)
  (P.posx,y⇒posx*y N.sixPos (P.posx,y⇒posx*y Guard.xPositive Guard.xPositive))
  (P.≃-trans h (P.≃-symm secondEquation))

-- Exact residual on the reverse-solved readouts. A producer of the
-- original normalized degree-41 germ need only establish this equation,
-- not re-prove any scalar jet cancellation or Ramanujan identity.
RayResidual : Set
RayResidual = Disk.literalResidual (Disk.A J.p first) (Disk.diskB J.p first second)
  (Packet.s2 ⋆) (Packet.s3 ⋆) (Packet.p2 ⋆) (Packet.p3 ⋆) ≃ R.0ℝ

signedFromRay : RayResidual → J.SignedJet
signedFromRay = Packet.signedJetFromActualFirst first second firstEquation secondEquation

-- Existing majorant/evaluation consumers, now with actual arithmetic.
rawFromRootAndRay : J.CMRoot → RayResidual → (k : Nat) → Raw.RawCross k
rawFromRootAndRay root h = Major.AtRoot.rawFromArithmeticAndCM root
  Ram.ramanujanX Ram.ramanujanY Ram.ramanujanE (signedFromRay h)

periodFromRootAndRay : J.CMRoot → RayResidual → Period.NativePeriod
periodFromRootAndRay root h = Raw.periodFromRaw (rawFromRootAndRay root h)

-- Original selected j, not a freely chosen root.
rawFromOriginalPacket :
  R._≤_ (R.∣ Iso.offset ∣) Iso.half →
  Packet.descending Guard.Root.j R.0ℝ Literal.diagonal ≃ R.0ℝ →
  RayResidual → (k : Nat) → Raw.RawCross k
rawFromOriginalPacket h d = rawFromRootAndRay (Packet.rootFromLiteralDiagonal h d)
