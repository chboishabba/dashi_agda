module DASHI.Physics.YangMills.BalabanClayGate4ConnectedTreeDecayExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Edgewise decay to connected-tree decay.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Once a connected activity is represented by a finite tree product and every
-- edge factor is bounded by q, induction bounds the complete product by q^m.
-- Tree counting and the entropy-versus-decay comparison are separate, already
-- handled by the rooted geometric modules.
------------------------------------------------------------------------

data _∈_ {A : Set} (selected : A) : List A → Set where
  here : ∀ {tail} → selected ∈ (selected ∷ tail)
  there : ∀ {head tail} → selected ∈ tail → selected ∈ (head ∷ tail)

record OrderedMultiplicativeDecay (Bound : Set) : Set₁ where
  field
    one : Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (multiply left right) (multiply leftUpper rightUpper)

open OrderedMultiplicativeDecay public

power :
  ∀ {Bound} → OrderedMultiplicativeDecay Bound → Bound → Nat → Bound
power algebra ratio zero = one algebra
power algebra ratio (suc exponent) =
  multiply algebra ratio (power algebra ratio exponent)

product :
  ∀ {Bound} → OrderedMultiplicativeDecay Bound → List Bound → Bound
product algebra [] = one algebra
product algebra (value ∷ values) =
  multiply algebra value (product algebra values)

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ values) = suc (length values)

finiteProductBelowPower :
  ∀ {Bound}
    (algebra : OrderedMultiplicativeDecay Bound)
    values ratio →
  (∀ value → value ∈ values → LessEqual algebra value ratio) →
  LessEqual algebra
    (product algebra values)
    (power algebra ratio (length values))
finiteProductBelowPower algebra [] ratio pointwise =
  reflexive algebra (one algebra)
finiteProductBelowPower algebra (value ∷ values) ratio pointwise =
  multiplyMonotone algebra
    (pointwise value here)
    (finiteProductBelowPower algebra values ratio
      (λ selected membership → pointwise selected (there membership)))

connectedTreeEdgeDecayLevel : ProofLevel
connectedTreeEdgeDecayLevel = machineChecked

physicalConnectedActivityTreeRepresentationInputsLevel : ProofLevel
physicalConnectedActivityTreeRepresentationInputsLevel = conditional

physicalGaugeEdgeDecayInputsLevel : ProofLevel
physicalGaugeEdgeDecayInputsLevel = conditional
