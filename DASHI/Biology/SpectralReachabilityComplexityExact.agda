module DASHI.Biology.SpectralReachabilityComplexityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Sanjeev Arora and Boaz Barak,
-- "Computational Complexity: A Modern Approach", Cambridge UP, 2009.
-- DOI: 10.1017/CBO9780511804090.
--
-- Ketan D. Mulmuley and Milind Sohoni,
-- "Geometric Complexity Theory I: An Approach to the P vs. NP and Related
-- Problems", SIAM Journal on Computing 31(2), 496-526.
-- DOI: 10.1137/S009753970038715X.
--
-- DASHI CONTRIBUTION
--
-- Supply the cost/reachability layer that a quotient or symmetry tower alone
-- does not contain.  We prove two generic exact theorems:
--   (1) a transition invariant separates unreachable states;
--   (2) a potential changing by at most c per step yields an n-step budget.
-- We also type the proposed input-size/depth/resolution carrier X[n,d,r] and a
-- fibre-witness cost interface.  No P-vs-NP separation or NP-completeness claim
-- is made by these interfaces.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Data.Nat.Properties as NatP

------------------------------------------------------------------------
-- Finite-step reachability.
------------------------------------------------------------------------

data ReachIn {State : Set} (Step : State → State → Set) :
  Nat → State → State → Set where
  reachZero : ∀ {x} → ReachIn Step zero x x
  reachStep : ∀ {n x y z} →
    Step x y → ReachIn Step n y z → ReachIn Step (suc n) x z

record StepInvariant {State : Set}
  (Step : State → State → Set) (Value : Set) : Set where
  constructor stepInvariant
  field
    Φ : State → Value
    preserved : ∀ {x y} → Step x y → Φ x ≡ Φ y

open StepInvariant public

reachPreservesInvariant :
  ∀ {State Value} {Step : State → State → Set}
    (invariant : StepInvariant Step Value)
    {n x y} → ReachIn Step n x y →
  Φ invariant x ≡ Φ invariant y
reachPreservesInvariant invariant reachZero = refl
reachPreservesInvariant invariant (reachStep step rest) =
  trans
    (preserved invariant step)
    (reachPreservesInvariant invariant rest)

invariantSeparatesNoReach :
  ∀ {State Value} {Step : State → State → Set}
    (invariant : StepInvariant Step Value)
    {n x y} →
  ¬ (Φ invariant x ≡ Φ invariant y) →
  ¬ ReachIn Step n x y
invariantSeparatesNoReach invariant unequal reach =
  unequal (reachPreservesInvariant invariant reach)

------------------------------------------------------------------------
-- Quantitative potential bound.
------------------------------------------------------------------------

record StepPotential {State : Set}
  (Step : State → State → Set) : Set where
  constructor stepPotential
  field
    potential : State → Nat
    perStepCost : Nat
    stepBound : ∀ {x y} →
      Step x y → potential y ≤ potential x + perStepCost

open StepPotential public

reachPotentialBound :
  ∀ {State} {Step : State → State → Set}
    (pot : StepPotential Step)
    {n x y} → ReachIn Step n x y →
  potential pot y
  ≤ potential pot x + n * perStepCost pot
reachPotentialBound pot reachZero
  rewrite NatP.+-identityʳ (potential pot _) = NatP.≤-refl
reachPotentialBound pot {n = suc n} {x = x} {y = z}
  (reachStep {y = y} step rest) =
  begin
    potential pot z
      ≤⟨ reachPotentialBound pot rest ⟩
    potential pot y + n * perStepCost pot
      ≤⟨ NatP.+-mono-≤ (stepBound pot step) NatP.≤-refl ⟩
    (potential pot x + perStepCost pot) + n * perStepCost pot
      ≡⟨ NatP.+-assoc (potential pot x) (perStepCost pot)
            (n * perStepCost pot) ⟩
    potential pot x + (perStepCost pot + n * perStepCost pot)
      ≡⟨⟩
    potential pot x + suc n * perStepCost pot
  ∎
  where open ≤-Reasoning

potentialBudgetSeparatesNoReach :
  ∀ {State} {Step : State → State → Set}
    (pot : StepPotential Step)
    {n x y} →
  ¬ (potential pot y
      ≤ potential pot x + n * perStepCost pot) →
  ¬ ReachIn Step n x y
potentialBudgetSeparatesNoReach pot violatesBudget reach =
  violatesBudget (reachPotentialBound pot reach)

------------------------------------------------------------------------
-- Third axis: computational input size n, relational/depth coordinate d,
-- observational resolution r.
------------------------------------------------------------------------

record ComplexityIndexedCarrier : Set₁ where
  constructor complexityIndexedCarrier
  field
    Carrier : Nat → Nat → Nat → Set
    coarsenResolution :
      ∀ {n d r} → Carrier n d (suc r) → Carrier n d r

open ComplexityIndexedCarrier public

------------------------------------------------------------------------
-- Search/verification cost lives on top of a fibre relation.  A Boolean
-- verifier and a search procedure/cost are distinct fields by construction.
------------------------------------------------------------------------

record FibreWitnessProblem : Set₁ where
  constructor fibreWitnessProblem
  field
    Input : Set
    Witness : Set
    inputSize : Input → Nat
    witnessSize : Witness → Nat
    inFibre : Input → Witness → Bool
    verify : Input → Witness → Bool
    verificationCost : Input → Witness → Nat
    searchCost : Input → Nat

open FibreWitnessProblem public

record PolynomialVerificationBound
  (problem : FibreWitnessProblem) : Set where
  constructor polynomialVerificationBound
  field
    exponent : Nat
    overhead : Nat
    verificationBound :
      (x : Input problem) (w : Witness problem) →
      verificationCost problem x w
      ≤ (inputSize problem x + witnessSize problem w) ^ exponent + overhead

record PolynomialSearchBound
  (problem : FibreWitnessProblem) : Set where
  constructor polynomialSearchBound
  field
    exponent : Nat
    overhead : Nat
    searchBound :
      (x : Input problem) →
      searchCost problem x
      ≤ inputSize problem x ^ exponent + overhead

-- The two bounds are separate types.  Supplying a polynomial verifier does not
-- definitionally or logically manufacture a polynomial search algorithm.
record VerifySearchSeparationInterface
  (problem : FibreWitnessProblem) : Set where
  constructor verifySearchSeparationInterface
  field
    verifierBound : PolynomialVerificationBound problem

------------------------------------------------------------------------
-- Symbol discipline: the analytic projection P and complexity class P share a
-- glyph in prose only.  They are represented by different typed tags here.
------------------------------------------------------------------------

data ProjectionOperatorTag : Set where
  coarseProjectionP : ProjectionOperatorTag

data ComplexityClassTag : Set where
  polynomialTimeP nondeterministicPolynomialTimeNP : ComplexityClassTag

record ComplexityBridgeClaimScope : Set where
  constructor complexityBridgeClaimScope
  field
    finiteReachabilityObstructionConstructed : Bool
    finiteReachabilityObstructionConstructedIsTrue :
      finiteReachabilityObstructionConstructed ≡ true

    quantitativePotentialBudgetConstructed : Bool
    quantitativePotentialBudgetConstructedIsTrue :
      quantitativePotentialBudgetConstructed ≡ true

    verificationAndSearchCostsTypedSeparately : Bool
    verificationAndSearchCostsTypedSeparatelyIsTrue :
      verificationAndSearchCostsTypedSeparately ≡ true

    pVersusNPResolved : Bool
    pVersusNPResolvedIsFalse : pVersusNPResolved ≡ false

    fibreWitnessProblemProvedNPComplete : Bool
    fibreWitnessProblemProvedNPCompleteIsFalse :
      fibreWitnessProblemProvedNPComplete ≡ false

canonicalComplexityBridgeClaimScope : ComplexityBridgeClaimScope
canonicalComplexityBridgeClaimScope =
  complexityBridgeClaimScope
    true refl
    true refl
    true refl
    false refl
    false refl
