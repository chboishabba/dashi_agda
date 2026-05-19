module DASHI.Physics.QuantumHistory where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.PhysicalTheory as PT
open import DASHI.Physics.SymmetryQuotient as SQ

record HistoryTheory (ℓ : Level) : Set (lsuc ℓ) where
  field
    Conf    : Set ℓ
    History : Conf → Conf → Set ℓ

    idH   : ∀ {x} → History x x
    _∘H_  : ∀ {x y z} → History y z → History x y → History x z

record AmplitudeCarrier (ℓ : Level) : Set (lsuc ℓ) where
  field
    Amp       : Set ℓ
    zero one  : Amp
    _+A_ _*A_ : Amp → Amp → Amp

record LinearSpaceLike {ℓ : Level}
  (K : AmplitudeCarrier ℓ) : Set (lsuc ℓ) where
  open AmplitudeCarrier K
  field
    Carrier : Set ℓ
    _+L_    : Carrier → Carrier → Carrier
    _·L_    : Amp → Carrier → Carrier
    zeroL   : Carrier

record QuantumHistory {ℓ : Level}
  (H : HistoryTheory ℓ)
  (K : AmplitudeCarrier ℓ) : Set (lsuc ℓ) where
  open HistoryTheory H
  open AmplitudeCarrier K
  field
    amp : ∀ {x y} → History x y → Amp

    amp-id :
      ∀ {x} → amp (idH {x = x}) ≡ one

    amp-compose :
      ∀ {x y z} (γ₂ : History y z) (γ₁ : History x y) →
      amp (γ₂ ∘H γ₁) ≡ (amp γ₂ *A amp γ₁)

record QuantumStateSpace {ℓ : Level} : Set (lsuc ℓ) where
  field
    Basis  : Set ℓ
    QState : Set ℓ

    basis : Basis → QState
    _+Q_  : QState → QState → QState

record SymmetricQuantumHistory {ℓ : Level}
  (S : SQ.SymmetricTheory ℓ)
  (H : HistoryTheory ℓ)
  (K : AmplitudeCarrier ℓ)
  (QH : QuantumHistory H K) : Set (lsuc ℓ) where
  field
    conf-align :
      HistoryTheory.Conf H ≡
      PT.State (SQ.SymmetricTheory.base S)

    actH :
      SQ.SymmetricTheory.Group S →
      ∀ {x y} →
      HistoryTheory.History H x y →
      HistoryTheory.History H x y

    amp-invariant :
      ∀ g {x y} (γ : HistoryTheory.History H x y) →
      QuantumHistory.amp QH (actH g γ) ≡ QuantumHistory.amp QH γ
