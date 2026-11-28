module DASHI.Moonshine.CM163BishopHecke41ActualJLogPhaseJetExact where

-- SOURCE-WRITTEN, kernel pending. Compose the original exponential
-- phase with the actual j two-jet. The exponent increment is the
-- logarithmic q coordinate, so the coefficients are Euler and half
-- Euler-squared, not independent derivatives of a new model.
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
open R using (_⋆)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.CM163BishopHecke41ActualJLocalSecondJetExact as Actual
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41SecondJetCalculusExact as J2
import DASHI.Moonshine.CM163BishopHecke41ComplexExpSecondJetExact as Exp
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_)

module At (inputs : Round11.BishopCutset) where
  module F = Actual.At inputs
  module Phase = J2.At inputs
  module G = F.G
  open F.O using (q)

  module Around (p : U.BishopUpperHalfPlanePoint) where
    module D = F.Around p
    half = Poly.realC ((+ 1 / 2) ⋆)

    euler1 eulerTaylor2 : BishopComplex
    euler1 = q p *C D.j1
    eulerTaylor2 = ((q p *C half) *C D.j1) +C (q p *C (q p *C D.j2))

    actualLogJet : (v : Nat → U.BishopUpperHalfPlanePoint) →
      (w : Nat → BishopComplex) →
      (∀ n → Phase.Ph.exponent (v n) ≈C (Phase.Ph.exponent p +C w n)) →
      (small : ∀ n → Exp.Inside (w n)) → Lim.Conv w A.zeroC →
      (inside : ∀ n → D.Ref.S.Inside (q (v n))) →
      J2.Jet2 w (λ n → G.j (v n)) (G.j p) euler1 eulerTaylor2
    actualLogJet v w phase small cv inside =
      let qJet = Phase.actualPhase2 p v w phase small cv
          qCv = J.continuous cv (J2.first qJet)
      in J2.compose cv qJet (D.actualJ v inside qCv)
