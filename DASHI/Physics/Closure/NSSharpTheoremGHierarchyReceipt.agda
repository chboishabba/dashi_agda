module DASHI.Physics.Closure.NSSharpTheoremGHierarchyReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record Level1DeterminantLedgerFacts : Set where
  constructor mkLevel1DeterminantLedgerFacts
  field
    betchovDetIdentityRecorded :
      String
    positiveMeasureLambda2GreaterThanZeroNearBlowUpRecorded :
      String
    delta1PositiveAlmostEverywhereOnDOmegaKRecorded :
      String
    level1HandoffRecorded :
      String

record Level2PromotableConditionalFacts : Set where
  constructor mkLevel2PromotableConditionalFacts
  field
    conditionalPromotionUnderHBAndHAreaAndDelta1Ge1Recorded :
      String
    hAreaMustBeRederivedViaDetSPlusNotQvelRecorded :
      String

record Level3OpenGates : Set where
  constructor mkLevel3OpenGates
  field
    delta1Ge1FromPDEAloneOpen :
      String
    hBStrictPositivityPropagationOpen :
      String
    uniformHAreaLowerBoundForOmegaKOpen :
      String

record NSSharpTheoremGHierarchyReceipt : Set where
  constructor mkNSSharpTheoremGHierarchyReceipt
  field
    hierarchySummary :
      String
    level1 :
      Level1DeterminantLedgerFacts
    level2 :
      Level2PromotableConditionalFacts
    level3 :
      Level3OpenGates
    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true
    theoremPromotion :
      Bool
    theoremPromotionIsFalse :
      theoremPromotion ≡ false
    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false

open Level1DeterminantLedgerFacts public
open Level2PromotableConditionalFacts public
open Level3OpenGates public
open NSSharpTheoremGHierarchyReceipt public

canonicalNSSharpTheoremGHierarchyReceipt :
  NSSharpTheoremGHierarchyReceipt
canonicalNSSharpTheoremGHierarchyReceipt =
  mkNSSharpTheoremGHierarchyReceipt
    "Old hierarchy: Qvel-sign-change and Omega_K were placed in Level 1, and type-I H_area was treated as already routed. Corrected hierarchy: Level 1 is the determinant-ledger proof row, Level 2 is the promotable conditional theorem, and Level 3 contains only open gates. Handoff: keep the receipt fail-closed and do not strengthen beyond the ledger."
    (mkLevel1DeterminantLedgerFacts
      "Level 1: the Betchov determinant identity is recorded as proved."
      "Level 1: near blow-up, the row {lambda2 > 0} is recorded as positive-measure."
      "Level 1: delta1 > 0 is recorded almost everywhere on dOmega_K."
      "Level 1 handoff: these unconditional rows feed the conditional lane without claiming a stronger theorem.")
    (mkLevel2PromotableConditionalFacts
      "Level 2: the promotable conditional theorem is recorded under H_B + H_area + delta1 >= 1."
      "Level 2 note: H_area must be rederived via det(S)+, not via Qvel.")
    (mkLevel3OpenGates
      "Level 3 open gate: deriving delta1 >= 1 from the PDE alone remains open."
      "Level 3 open gate: strict positivity propagation for H_B remains open."
      "Level 3 open gate: a uniform lower bound for H_area on Omega_K remains open.")
    true
    refl
    false
    refl
    false
    refl
