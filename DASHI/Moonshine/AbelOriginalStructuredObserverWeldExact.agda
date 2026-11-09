module DASHI.Moonshine.AbelOriginalStructuredObserverWeldExact where

-- The actual existing JCoarse/JFine observer is a fine-point observer,
-- not necessarily a function of modular j alone.
-- Keep its lift and commuting square explicit.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Moonshine.JInvariantTetrationAbelModularTransportExact as T
import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.JInvariantAnalyticJCoarseFineObserverExact as Observer
import DASHI.Moonshine.JInvariantJCoarseFineElevenTritChartShiftExact as Chart
import DASHI.Moonshine.JInvariantRiemannObserverResidualSufficiencyBidiExact as Residual

record OriginalFineObserverAbelSquare
  (S : T.AbelModularExpSystem)
  (M : Modular.ModularJFrickeSystem)
  (O : Observer.AnalyticJStructuredObserver M) : Set₁ where
  field
    toFine : T.Coordinate S → Modular.FinePoint M
    fineTranslation : Modular.FinePoint M → Modular.FinePoint M
    abelFineTranslation :
      (tau : T.Coordinate S) →
      toFine (T.translate S tau) ≡ fineTranslation (toFine tau)
    fineObserverTranslation :
      (p : Modular.FinePoint M) →
      Observer.observe O (fineTranslation p) ≡ Observer.observe O p

open OriginalFineObserverAbelSquare public

originalFineToCoarseObserverIntertwines :
  (S : T.AbelModularExpSystem) →
  (M : Modular.ModularJFrickeSystem) →
  (O : Observer.AnalyticJStructuredObserver M) →
  (W : OriginalFineObserverAbelSquare S M O) →
  (w : T.Point S) →
  Observer.observe O (toFine W (T.abel S (T.exponential S w)))
  ≡
  Observer.observe O (toFine W (T.abel S w))
originalFineToCoarseObserverIntertwines S M O W w =
  trans
    (cong (λ tau → Observer.observe O (toFine W tau))
      (T.abelExponentialLaw S w))
    (trans
      (cong (Observer.observe O)
        (abelFineTranslation W (T.abel S w)))
      (fineObserverTranslation W (toFine W (T.abel S w))))

originalLocal27UnderExponentiation :
  (S : T.AbelModularExpSystem) →
  (M : Modular.ModularJFrickeSystem) →
  (O : Observer.AnalyticJStructuredObserver M) →
  (W : OriginalFineObserverAbelSquare S M O) →
  (w : T.Point S) →
  Observer.observeLocal27 O
    (toFine W (T.abel S (T.exponential S w)))
  ≡
  Observer.observeLocal27 O (toFine W (T.abel S w))
originalLocal27UnderExponentiation S M O W w =
  cong
    (λ state →
      Residual.localJObserver (Observer.structuredFieldOfChart state))
    (originalFineToCoarseObserverIntertwines S M O W w)
