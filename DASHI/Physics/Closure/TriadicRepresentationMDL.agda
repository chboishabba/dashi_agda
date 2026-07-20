module DASHI.Physics.Closure.TriadicRepresentationMDL where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Representation families available to the selector.

data DescriptionClass : Set where
  rawTrits : DescriptionClass
  finiteQuotient : DescriptionClass
  irrepBlocks : DescriptionClass
  modularCoordinates : DescriptionClass
  ellipticModuli : DescriptionClass

------------------------------------------------------------------------
-- Finite depth index 0 .. bound-1.

data DepthBelow : Nat → Set where
  depthZero : ∀ {n : Nat} → DepthBelow (suc n)
  depthNext :
    ∀ {n : Nat} →
    DepthBelow n →
    DepthBelow (suc n)

depthValue : ∀ {n : Nat} → DepthBelow n → Nat
depthValue depthZero = zero
depthValue (depthNext d) = suc (depthValue d)

record BoundedDescription (bound : Nat) : Set where
  constructor bounded-description
  field
    descriptionClass : DescriptionClass
    depthIndex : DepthBelow bound

open BoundedDescription public

------------------------------------------------------------------------
-- Description plus residual objective.

record RepresentationCostModel : Set₁ where
  field
    Cost : Set
    _≤ᶜ_ : Cost → Cost → Set
    _+ᶜ_ : Cost → Cost → Cost

    representationCost :
      DescriptionClass →
      Nat →
      Cost

    residualCost :
      DescriptionClass →
      Nat →
      Cost

open RepresentationCostModel public

totalCost :
  RepresentationCostModel →
  DescriptionClass →
  Nat →
  RepresentationCostModel.Cost
    (λ where) 
totalCost = λ where

------------------------------------------------------------------------
-- A helper record avoids relying on implicit projection inference for Cost.

record CostedDescription
  (M : RepresentationCostModel) : Set where
  constructor costed-description
  field
    class : DescriptionClass
    depth : Nat
    cost : Cost M
    costMatchesObjective : Set

open CostedDescription public

objective :
  (M : RepresentationCostModel) →
  DescriptionClass →
  Nat →
  Cost M
objective M c n =
  _+ᶜ_ M
    (representationCost M c n)
    (residualCost M c n)

------------------------------------------------------------------------
-- Exact bounded minimizer receipt.

record BoundedRepresentationMDL
  (M : RepresentationCostModel)
  (bound : Nat) : Set₁ where
  field
    selected : BoundedDescription bound

    selectedIsMinimal :
      (candidate : BoundedDescription bound) →
      _≤ᶜ_ M
        (objective M
          (descriptionClass selected)
          (depthValue (depthIndex selected)))
        (objective M
          (descriptionClass candidate)
          (depthValue (depthIndex candidate)))

open BoundedRepresentationMDL public

------------------------------------------------------------------------
-- Coding and statistical gates for asymptotic claims.

record KraftCodeGate : Set₁ where
  field
    Codeword : Set
    encodeClass : DescriptionClass → Codeword
    codeLength : Codeword → Nat
    prefixFreeOrKraftValid : Set

open KraftCodeGate public

record RepresentationMDLConsistencyGate
  (M : RepresentationCostModel) : Set₁ where
  field
    SampleSize : Set
    Data : Set
    stochasticDataLaw : Set

    maximumDepthAtSample : SampleSize → Nat
    selectedClassAtSample : SampleSize → DescriptionClass
    selectedDepthAtSample : SampleSize → Nat

    kraftGate : KraftCodeGate
    identifiabilityOrOracleCondition : Set
    modelClassGrowthControlled : Set
    concentrationOrErgodicity : Set

    riskConsistency : Set
    trueDepthRecoveryWhenIdentifiable : Set

open RepresentationMDLConsistencyGate public

------------------------------------------------------------------------
-- Explicit claim boundary.

mdlStatement : String
mdlStatement =
  "MDL selects jointly over representation family and depth: raw trits, finite quotient coordinates, irrep blocks, certified modular coordinates, or elliptic moduli plus retained level data."

mdlBoundary : String
mdlBoundary =
  "A bounded minimizer is an exact finite receipt. Kraft validity, stochastic assumptions, class-growth control, concentration or ergodicity, oracle consistency, and true-depth recovery are separate asymptotic gates."
