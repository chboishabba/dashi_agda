module DASHI.Moonshine.AbelBishopOriginalExponentialIteratesExact where

-- Native, setoid-respecting iterations of the actual Bishop
-- complex power-series exponential, not a generic function field.
-- No global Abel coordinate, logarithm inverse or Kneser chart is assumed.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Analysis.BishopSetoidComplexExact as Exp
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Series
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld

originalBishopExpIter :
  Exp.BishopSetoidComplexTranscendentals →
  Nat → Exp.BishopComplex → Exp.BishopComplex
originalBishopExpIter T zero z = z
originalBishopExpIter T (suc n) z =
  Exp.expC T (originalBishopExpIter T n z)

originalBishopExpIterCongruent :
  (T : Exp.BishopSetoidComplexTranscendentals) →
  (n : Nat) →
  ∀ {x y : Exp.BishopComplex} →
  Exp._≈C_ x y →
  Exp._≈C_ (originalBishopExpIter T n x)
             (originalBishopExpIter T n y)
originalBishopExpIterCongruent T zero equivalent = equivalent
originalBishopExpIterCongruent T (suc n) equivalent =
  Exp.expCongruent T
    (originalBishopExpIterCongruent T n equivalent)

originalBishopExpSeriesIter :
  Exp.BishopSetoidComplexTranscendentals →
  Nat → Series.BishopComplex → Series.BishopComplex
originalBishopExpSeriesIter T zero z = z
originalBishopExpSeriesIter T (suc n) z =
  Weld.originalBishopExpOnSeries T
    (originalBishopExpSeriesIter T n z)

originalBishopExpSeriesIterCongruent :
  (T : Exp.BishopSetoidComplexTranscendentals) →
  (n : Nat) →
  ∀ {x y : Series.BishopComplex} →
  Series._≈C_ x y →
  Series._≈C_
    (originalBishopExpSeriesIter T n x)
    (originalBishopExpSeriesIter T n y)
originalBishopExpSeriesIterCongruent T zero equivalent = equivalent
originalBishopExpSeriesIterCongruent T (suc n) equivalent =
  Weld.originalBishopExpOnSeriesCongruent T
    (originalBishopExpSeriesIterCongruent T n equivalent)

originalBishopExpIterSameSource :
  (T : Exp.BishopSetoidComplexTranscendentals) →
  (n : Nat) →
  (z : Exp.BishopComplex) →
  Weld.toSeries (originalBishopExpIter T n z) ≡
  originalBishopExpSeriesIter T n (Weld.toSeries z)
originalBishopExpIterSameSource T zero z = refl
originalBishopExpIterSameSource T (suc n) z
  rewrite originalBishopExpIterSameSource T n z = refl
