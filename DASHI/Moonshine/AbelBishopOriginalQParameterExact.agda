module DASHI.Moonshine.AbelBishopOriginalQParameterExact where

-- The original Bishop exp/sin/cos complex exponential and selected
-- Round11 Machin pi define literal q(tau)=exp_C(2*pi*i*tau).
-- No T-periodicity is assumed or proved here.

open import Agda.Builtin.Nat using (suc; zero)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.BishopSetoidComplexExact as Complex
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Series
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Round11
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Cutset

originalTwoPiI :
  (T : Complex.BishopSetoidComplexTranscendentals) →
  Complex.BishopComplex
originalTwoPiI T =
  Complex.scaleNatC (suc (suc zero))
    (Complex._*C_ Complex.imaginaryUnit (Complex.piC T))

originalBishopQAt :
  (T : Complex.BishopSetoidComplexTranscendentals) →
  Complex.BishopComplex → Complex.BishopComplex
originalBishopQAt T tau =
  Complex.expC T (Complex._*C_ (originalTwoPiI T) tau)

originalBishopQAtCongruent :
  (T : Complex.BishopSetoidComplexTranscendentals) →
  ∀ {left right : Complex.BishopComplex} →
  Complex._≈C_ left right →
  Complex._≈C_ (originalBishopQAt T left) (originalBishopQAt T right)
originalBishopQAtCongruent T eq =
  Complex.expCongruent T
    (Complex.mulCongruent
      (Complex.≈C-refl (originalTwoPiI T))
      eq)

originalBishopQAtForSeries :
  (T : Complex.BishopSetoidComplexTranscendentals) →
  Series.BishopComplex → Series.BishopComplex
originalBishopQAtForSeries T tau =
  Weld.toSeries (originalBishopQAt T (Weld.toExponential tau))

originalBishopQAtSeriesCongruent :
  (T : Complex.BishopSetoidComplexTranscendentals) →
  ∀ {left right : Series.BishopComplex} →
  Series._≈C_ left right →
  Series._≈C_
    (originalBishopQAtForSeries T left)
    (originalBishopQAtForSeries T right)
originalBishopQAtSeriesCongruent T eq =
  Weld.originalExpEquivalenceToSeries
    (originalBishopQAtCongruent T
      (Weld.originalSeriesEquivalenceToExp eq))

originalBishopQAtSourceIdentified :
  (T : Complex.BishopSetoidComplexTranscendentals) →
  (tau : Complex.BishopComplex) →
  originalBishopQAtForSeries T (Weld.toSeries tau)
  ≡ Weld.toSeries (originalBishopQAt T tau)
originalBishopQAtSourceIdentified T (Complex.complex a b) = refl

originalRound11MachinQAt :
  Cutset.Round11BishopCutset →
  Complex.BishopComplex → Complex.BishopComplex
originalRound11MachinQAt inputs =
  originalBishopQAt (Round11.round11MachinTranscendentals inputs)

originalRound11MachinQAtForSeries :
  Cutset.Round11BishopCutset →
  Series.BishopComplex → Series.BishopComplex
originalRound11MachinQAtForSeries inputs =
  originalBishopQAtForSeries (Round11.round11MachinTranscendentals inputs)
