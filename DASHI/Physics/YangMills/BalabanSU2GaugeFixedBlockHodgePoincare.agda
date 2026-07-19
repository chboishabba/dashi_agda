module DASHI.Physics.YangMills.BalabanSU2GaugeFixedBlockHodgePoincare where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record OrderedEnergy {s : Level} (Scalar : Set s) : Set (lsuc s) where
  field
    _≤_ : Scalar → Scalar → Set s
    add : Scalar → Scalar → Scalar
    transitive : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    addMonotoneRight : ∀ fixed {a b} → a ≤ b → add fixed a ≤ add fixed b
open OrderedEnergy public

-- The exact gauge-fixed energy appearing at trivial background.
gaugeFixedEnergy :
  ∀ {s} {Scalar : Set s} →
  OrderedEnergy Scalar →
  Scalar → Scalar → Scalar → Scalar
gaugeFixedEnergy order curlEnergy divergenceEnergy averageEnergy =
  add order curlEnergy (add order divergenceEnergy averageEnergy)

-- Local oscillation control plus block-mean control yields the global
-- block Hodge--Poincare inequality.  This is the geometric proof attack in its
-- minimal exact form; the two premises are the concrete lattice lemmas to solve.
blockHodgePoincareFromLocal :
  ∀ {s} {Scalar : Set s}
  (order : OrderedEnergy Scalar)
  (normEnergy differentialEnergy meanEnergy averageEnergy : Scalar) →
  _≤_ order normEnergy (add order differentialEnergy meanEnergy) →
  _≤_ order meanEnergy averageEnergy →
  _≤_ order normEnergy (add order differentialEnergy averageEnergy)
blockHodgePoincareFromLocal
  order normEnergy differentialEnergy meanEnergy averageEnergy
  localOscillation meanControlled =
  transitive order localOscillation
    (addMonotoneRight order differentialEnergy meanControlled)

record GaugeFixedBlockHodgePoincare
  {v s : Level}
  (Vector : Set v)
  (Scalar : Set s)
  (order : OrderedEnergy Scalar) : Set (lsuc (v ⊔ s)) where
  field
    normSquared : Vector → Scalar
    curlEnergy : Vector → Scalar
    divergenceEnergy : Vector → Scalar
    averageEnergy : Vector → Scalar
    constantWeightedEnergy : Vector → Scalar
    weightedEnergyDefinition : ∀ vector →
      constantWeightedEnergy vector ≡
      gaugeFixedEnergy order
        (curlEnergy vector)
        (divergenceEnergy vector)
        (averageEnergy vector)
    hodgePoincare : ∀ vector →
      _≤_ order (normSquared vector) (constantWeightedEnergy vector)
open GaugeFixedBlockHodgePoincare public

record ZeroBackgroundCoercivity
  {v s : Level}
  (Vector : Set v)
  (Scalar : Set s)
  (order : OrderedEnergy Scalar) : Set (lsuc (v ⊔ s)) where
  field
    normSquared : Vector → Scalar
    hessianEnergy : Vector → Scalar
    coercive : ∀ vector → _≤_ order (normSquared vector) (hessianEnergy vector)
open ZeroBackgroundCoercivity public

hodgePoincareGivesZeroBackgroundCoercivity :
  ∀ {v s} {Vector : Set v} {Scalar : Set s}
  (order : OrderedEnergy Scalar)
  (hodge : GaugeFixedBlockHodgePoincare Vector Scalar order)
  (hessianEnergy : Vector → Scalar) →
  (∀ vector → hessianEnergy vector ≡ constantWeightedEnergy hodge vector) →
  ZeroBackgroundCoercivity Vector Scalar order
hodgePoincareGivesZeroBackgroundCoercivity order hodge hessianEnergy energyIdentity =
  record
    { normSquared = normSquared hodge
    ; hessianEnergy = hessianEnergy
    ; coercive = λ vector →
        transitive order
          (hodgePoincare hodge vector)
          (rewriteRight vector)
    }
  where
    rewriteRight : ∀ vector →
      _≤_ order
        (constantWeightedEnergy hodge vector)
        (hessianEnergy vector)
    rewriteRight vector
      rewrite energyIdentity vector =
      hodgePoincare hodge vector

-- A perturbative background proof should produce the two explicit comparison
-- inequalities below.  Their composition is the uniform small-field coercivity
-- theorem; no background positivity is assumed as a record field.
backgroundCoercivityFromPerturbation :
  ∀ {s} {Scalar : Set s}
  (order : OrderedEnergy Scalar)
  (norm baseEnergy backgroundEnergy loss absorbedEnergy : Scalar) →
  _≤_ order norm baseEnergy →
  _≤_ order baseEnergy (add order backgroundEnergy loss) →
  _≤_ order (add order backgroundEnergy loss) absorbedEnergy →
  _≤_ order norm absorbedEnergy
backgroundCoercivityFromPerturbation
  order norm baseEnergy backgroundEnergy loss absorbedEnergy
  baseCoercive perturbationComparison lossAbsorbed =
  transitive order baseCoercive
    (transitive order perturbationComparison lossAbsorbed)
