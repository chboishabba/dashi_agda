module DASHI.Physics.Closure.NSSharpTheoremGHierarchyReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record Level1UnconditionalFacts : Set where
  constructor mkLevel1UnconditionalFacts
  field
    qVelZeroMeanRecorded :
      String
    omegaKPositiveMeasureRecorded :
      String
    boundaryLambda2CancellationRecorded :
      String
    theoremGSourceRecorded :
      String

record Level2TypeIConditionalFacts : Set where
  constructor mkLevel2TypeIConditionalFacts
  field
    conditionalNoBlowupStatement :
      String
    hAreaUniformUnderTypeIRecorded :
      String

record Level3OpenGates : Set where
  constructor mkLevel3OpenGates
  field
    delta1GreaterThanOneFromPDEAloneOpen :
      String
    hBStrictPositivityPropagationOpen :
      String
    hAreaUnderTypeIIOpen :
      String

record NSSharpTheoremGHierarchyReceipt : Set where
  constructor mkNSSharpTheoremGHierarchyReceipt
  field
    level1 :
      Level1UnconditionalFacts
    level2 :
      Level2TypeIConditionalFacts
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

open Level1UnconditionalFacts public
open Level2TypeIConditionalFacts public
open Level3OpenGates public
open NSSharpTheoremGHierarchyReceipt public

canonicalNSSharpTheoremGHierarchyReceipt :
  NSSharpTheoremGHierarchyReceipt
canonicalNSSharpTheoremGHierarchyReceipt =
  mkNSSharpTheoremGHierarchyReceipt
    (mkLevel1UnconditionalFacts
      "Level 1: the Qvel zero-mean identity is recorded unconditionally."
      "Level 1: for nontrivial times, Omega_K and its complement are recorded as positive-measure sets."
      "Level 1: the exact boundary cancellation lambda2 * |<omega,e2>|^2 = 0 on {lambda2 = 0} is recorded."
      "Level 1: the TheoremG source lane is recorded as enstrophy-controlled rather than H5-controlled.")
    (mkLevel2TypeIConditionalFacts
      "Level 2: type I + delta1 > 1 + H_B implies T* = infinity is recorded as a conditional no-blowup route."
      "Level 2: H_area is recorded as uniform under type I.")
    (mkLevel3OpenGates
      "Level 3 open gate: deriving delta1 > 1 from PDE alone remains open."
      "Level 3 open gate: strict positivity propagation for H_B remains open."
      "Level 3 open gate: H_area under type II remains open.")
    true
    refl
    false
    refl
    false
    refl
