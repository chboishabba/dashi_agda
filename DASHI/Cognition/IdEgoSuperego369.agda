module DASHI.Cognition.IdEgoSuperego369 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import Base369 as Base
import DASHI.Cognition.Base369ZeroFibre as Fibre

------------------------------------------------------------------------
-- Role interpretation of the existing 3-6-9 carriers.
--
-- These are typed cognitive roles, not claims that psychoanalytic vocabulary
-- is a literal neural anatomy:
--
--   3 : immediate valuation / pre-reflexive Id carrier
--   6 : valuation plus a self/other or forward/reverse reflexive split
--   9 : one ternary valuation evaluated against another ternary valuation
--
-- Categorical identity is written separately as identityMorphism below; it is
-- not conflated with the psychoanalytic Id role.
------------------------------------------------------------------------

data PsychoStage : Set where
  idStage egoStage superegoStage : PsychoStage

IdCarrier : Set
IdCarrier = Base.TriTruth

EgoCarrier : Set
EgoCarrier = Fibre.SixCoordinates

SuperegoCarrier : Set
SuperegoCarrier = Fibre.NineCoordinates

idToEgo : IdCarrier → Fibre.Orientation → EgoCarrier
idToEgo value orientation = Fibre.sixCoordinates value orientation

egoToId : EgoCarrier → IdCarrier
egoToId = Fibre.polarity

idToSuperego : IdCarrier → Base.TriTruth → SuperegoCarrier
idToSuperego felt normative = Fibre.nineCoordinates felt normative

superegoToId : SuperegoCarrier → IdCarrier
superegoToId = Fibre.localValue

egoProjectionReturnsId :
  (value : IdCarrier) → (orientation : Fibre.Orientation) →
  egoToId (idToEgo value orientation) ≡ value
egoProjectionReturnsId value orientation = refl

superegoProjectionReturnsId :
  (felt normative : Base.TriTruth) →
  superegoToId (idToSuperego felt normative) ≡ felt
superegoProjectionReturnsId felt normative = refl

------------------------------------------------------------------------
-- Felt, desired and compelled self coordinates.
------------------------------------------------------------------------

record SelfTriad : Set where
  constructor selfTriad
  field
    feltSelf      : Base.TriTruth
    desiredSelf   : Base.TriTruth
    compelledSelf : Base.TriTruth

open SelfTriad public

canonicalContestedSelf : SelfTriad
canonicalContestedSelf = selfTriad
  Base.tri-mid
  Base.tri-high
  Base.tri-low

feltNormativePair : SelfTriad → SuperegoCarrier
feltNormativePair self = idToSuperego (feltSelf self) (compelledSelf self)

desiredNormativePair : SelfTriad → SuperegoCarrier
desiredNormativePair self = idToSuperego (feltSelf self) (desiredSelf self)

feltCoordinateSurvivesNormativePair :
  (self : SelfTriad) →
  superegoToId (feltNormativePair self) ≡ feltSelf self
feltCoordinateSurvivesNormativePair self = refl

------------------------------------------------------------------------
-- Finite discrepancy pressure.  This is not a clinical measure; it is the
-- exact mismatch count among the three ternary self coordinates.
------------------------------------------------------------------------

triEqual : Base.TriTruth → Base.TriTruth → Nat
triEqual Base.tri-low Base.tri-low = 0
triEqual Base.tri-mid Base.tri-mid = 0
triEqual Base.tri-high Base.tri-high = 0
triEqual _ _ = 1

selfDiscrepancy : SelfTriad → Nat
selfDiscrepancy self =
  triEqual (feltSelf self) (desiredSelf self) +
  triEqual (feltSelf self) (compelledSelf self)

canonicalContestedSelfHasTwoDiscrepancies :
  selfDiscrepancy canonicalContestedSelf ≡ 2
canonicalContestedSelfHasTwoDiscrepancies = refl

------------------------------------------------------------------------
-- Reflexive split and identity notation.
------------------------------------------------------------------------

record ReflexiveSelf : Set where
  constructor reflexiveSelf
  field
    immediateValue : IdCarrier
    observingSide  : Fibre.Orientation

identityMorphism : ∀ {A : Set} → A → A
identityMorphism value = value

identityMorphismLeavesIdCarrierFixed :
  (value : IdCarrier) → identityMorphism value ≡ value
identityMorphismLeavesIdCarrierFixed value = refl
