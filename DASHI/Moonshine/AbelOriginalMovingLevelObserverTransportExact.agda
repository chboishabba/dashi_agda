module DASHI.Moonshine.AbelOriginalMovingLevelObserverTransportExact where

-- Modular j can be invariant while the genuine 27/9/3 cusp-level observers
-- rotate. This is an EQUIVARIANT square, not false observer invariance.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Moonshine.JInvariantTetrationAbelModularTransportExact as Abel
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Tower
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Level
import DASHI.Foundations.TriadicFiniteQuotient as Q

record OriginalMovingLevelAbelWeld
  (S : Abel.AbelModularExpSystem)
  (R : Render.JPhaseRenderingAlgebra)
  (L : Tower.CanonicalLevel27Lift R)
  (T : Tower.Level27TranslationLift R L) : Set₁ where
  field
    sourcePoint : Abel.Coordinate S → Klein.Point (Render.klein R)
    translatePointCommutes :
      (tau : Abel.Coordinate S) →
      sourcePoint (Abel.translate S tau) ≡
      Tower.translatePoint T (sourcePoint tau)

open OriginalMovingLevelAbelWeld public

originalMovingLevel27UnderExp :
  (S : Abel.AbelModularExpSystem) →
  (R : Render.JPhaseRenderingAlgebra) →
  (L : Tower.CanonicalLevel27Lift R) →
  (T : Tower.Level27TranslationLift R L) →
  (W : OriginalMovingLevelAbelWeld S R L T) →
  (w : Abel.Point S) →
  Tower.canonicalObserver27At L
    (sourcePoint W (Abel.abel S (Abel.exponential S w)))
  ≡
  Level.translateObserver27
    (Tower.canonicalObserver27At L
      (sourcePoint W (Abel.abel S w)))
originalMovingLevel27UnderExp S R L T W w =
  trans
    (cong (λ tau → Tower.canonicalObserver27At L (sourcePoint W tau))
      (Abel.abelExponentialLaw S w))
    (trans
      (cong (Tower.canonicalObserver27At L)
        (translatePointCommutes W (Abel.abel S w)))
      (Tower.observer27TranslationCommutes T
        (sourcePoint W (Abel.abel S w))))

originalMovingLevel9UnderExp :
  (S : Abel.AbelModularExpSystem) →
  (R : Render.JPhaseRenderingAlgebra) →
  (L : Tower.CanonicalLevel27Lift R) →
  (T : Tower.Level27TranslationLift R L) →
  (W : OriginalMovingLevelAbelWeld S R L T) →
  (w : Abel.Point S) →
  Tower.canonicalObserver9At L
    (sourcePoint W (Abel.abel S (Abel.exponential S w)))
  ≡
  Level.translateObserver9
    (Tower.canonicalObserver9At L
      (sourcePoint W (Abel.abel S w)))
originalMovingLevel9UnderExp S R L T W w =
  trans
    (cong (λ tau → Tower.canonicalObserver9At L (sourcePoint W tau))
      (Abel.abelExponentialLaw S w))
    (trans
      (cong (Tower.canonicalObserver9At L)
        (translatePointCommutes W (Abel.abel S w)))
      (Tower.observer9TranslationCommutes T
        (sourcePoint W (Abel.abel S w))))

originalMovingLevel3UnderExp :
  (S : Abel.AbelModularExpSystem) →
  (R : Render.JPhaseRenderingAlgebra) →
  (L : Tower.CanonicalLevel27Lift R) →
  (T : Tower.Level27TranslationLift R L) →
  (W : OriginalMovingLevelAbelWeld S R L T) →
  (w : Abel.Point S) →
  Tower.canonicalLevel3At L
    (sourcePoint W (Abel.abel S (Abel.exponential S w)))
  ≡
  Level.translateTriadic Q.one
    (Tower.canonicalLevel3At L
      (sourcePoint W (Abel.abel S w)))
originalMovingLevel3UnderExp S R L T W w =
  trans
    (cong (λ tau → Tower.canonicalLevel3At L (sourcePoint W tau))
      (Abel.abelExponentialLaw S w))
    (trans
      (cong (Tower.canonicalLevel3At L)
        (translatePointCommutes W (Abel.abel S w)))
      (Tower.level3TranslationDerived T
        (sourcePoint W (Abel.abel S w))))
