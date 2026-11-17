module DASHI.Physics.Gravity.KSW668F8ThreeChannelElectricWeylDefectTransportExact where

-- Original ell=0,2,4 linear TT harmonic receiver transport at t=4/3.
-- The componentwise electric-Weyl/SMS defect is transported by the
-- SAME finite sum without independently modifying channel sources.
-- ASSUMPTION: each component admits the original tensor TT/gauge
-- field and same-metric geometric defect. Not a discrete TT theorem.
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668F8OriginalElectricWeylDefectSliceExact as Single

alpha beta : ℚ
alpha = (+ 41) / 40
beta = (+ 3) / 16

record TTChannelDefectAtOriginalSlice : Set where
  field
    electric : ℚ
    sms : ℚ
    normalResidual : ℚ
    bulkResidual : ℚ
    sameOriginalDefect :
      electric + - sms
      ≡ - (alpha * normalResidual) + - (beta * bulkResidual)
open TTChannelDefectAtOriginalSlice public

three : ℚ → ℚ → ℚ → ℚ
three a b c = (a + b) + c

receiverDifferenceDistributes :
  (a b c x y z : ℚ) →
  three a b c + - (three x y z)
  ≡ three (a + - x) (b + - y) (c + - z)
receiverDifferenceDistributes a b c x y z = solve []

originalThreeChannelDefect :
  (a b c : TTChannelDefectAtOriginalSlice) →
  three (electric a) (electric b) (electric c)
    + - (three (sms a) (sms b) (sms c))
  ≡ - (alpha * three (normalResidual a)
                         (normalResidual b) (normalResidual c))
      + - (beta * three (bulkResidual a)
                         (bulkResidual b) (bulkResidual c))
originalThreeChannelDefect a b c
  rewrite receiverDifferenceDistributes
    (electric a) (electric b) (electric c)
    (sms a) (sms b) (sms c)
    | sameOriginalDefect a
    | sameOriginalDefect b
    | sameOriginalDefect c
  = solve []
