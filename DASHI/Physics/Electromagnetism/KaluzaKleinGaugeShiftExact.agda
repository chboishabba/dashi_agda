module DASHI.Physics.Electromagnetism.KaluzaKleinGaugeShiftExact where

-- Exact additive algebra behind the local KK connection theta = dy + k A.
-- Model: gauge shift dy' = dy - k dchi, A' = A + dchi.
-- Does NOT assert smoothness, scalar-curvature decomposition or Einstein equations.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

record AdditiveGroup (Carrier : Set) : Set where
  field
    zero : Carrier
    plus : Carrier → Carrier → Carrier
    neg : Carrier → Carrier
    assoc : ∀ a b c → plus (plus a b) c ≡ plus a (plus b c)
    leftUnit : ∀ a → plus zero a ≡ a
    rightUnit : ∀ a → plus a zero ≡ a
    rightInverse : ∀ a → plus a (neg a) ≡ zero
    comm : ∀ a b → plus a b ≡ plus b a
open AdditiveGroup

module Gauge (Form : Set) (G : AdditiveGroup Form) where
  _⊕_ = plus G
  minus = neg G

  kkConnection : Form → Form → Form
  kkConnection vertical potential = vertical ⊕ potential

  gaugePotential : Form → Form → Form
  gaugePotential potential displacement = potential ⊕ displacement

  gaugeVertical : Form → Form → Form
  gaugeVertical vertical displacement = vertical ⊕ minus displacement

  gaugeInvariant :
    ∀ vertical potential displacement →
    kkConnection (gaugeVertical vertical displacement)
                 (gaugePotential potential displacement)
      ≡ kkConnection vertical potential
  gaugeInvariant vertical potential displacement =
    trans (assoc G vertical (minus displacement)
             (potential ⊕ displacement))
    (trans (cong (λ x → vertical ⊕ x)
              (trans (sym (assoc G (minus displacement) potential displacement))
                (trans (cong (λ x → x ⊕ displacement)
                          (comm G (minus displacement) potential))
                  (trans (assoc G potential (minus displacement) displacement)
                    (trans (cong (λ x → potential ⊕ x)
                                  (comm G (minus displacement) displacement))
                      (trans (cong (λ x → potential ⊕ x)
                                    (rightInverse G displacement))
                        (rightUnit G potential)))))))
           refl)

  -- The KK ansatz's fibre part phi² (dy + k A)² is unchanged under the
  -- local gauge transformation if phi is held fixed.
  gaugeInvariantUnderObservable :
    ∀ {Observable : Set} (observe : Form → Observable)
      vertical potential displacement →
    observe (kkConnection (gaugeVertical vertical displacement)
                         (gaugePotential potential displacement))
      ≡ observe (kkConnection vertical potential)
  gaugeInvariantUnderObservable observe vertical potential displacement =
    cong observe (gaugeInvariant vertical potential displacement)
