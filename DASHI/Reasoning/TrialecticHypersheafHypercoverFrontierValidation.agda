module DASHI.Reasoning.TrialecticHypersheafHypercoverFrontierValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticHypersheafHypercoverFrontierExact as Frontier

boundary : Frontier.TrialecticHypersheafHypercoverFrontierBoundary
boundary = Frontier.canonicalTrialecticHypersheafHypercoverFrontierBoundary

higherStackReady : Frontier.higherStackPrerequisiteReady boundary ≡ true
higherStackReady = refl

hyperfabricReady : Frontier.typedHyperfabricPrerequisiteReady boundary ≡ true
hyperfabricReady = refl

effectiveDescentReady :
  Frontier.effectiveObjectMorphismDescentReady boundary ≡ true
effectiveDescentReady = refl

twoCellCocycleReady : Frontier.generalTwoCellCocycleReady boundary ≡ true
twoCellCocycleReady = refl

policyDepthReady : Frontier.policyIndexedDepthReady boundary ≡ true
policyDepthReady = refl

directHypercoverApiNotYetFound :
  Frontier.directHypercoverAPIAlreadyFoundInRepo boundary ≡ false
directHypercoverApiNotYetFound = refl

truncationHypercompleteWeldNotYetPaid :
  Frontier.truncationHypercompleteTheoremAlreadyWelded boundary ≡ false
truncationHypercompleteWeldNotYetPaid = refl

allOtherPrerequisitesPaid :
  Frontier.allNonHypercoverPrerequisitesPaid boundary ≡ true
allOtherPrerequisitesPaid = refl

singleTypedFrontier :
  Frontier.hypersheafPromotionNowHasSingleTypedFrontier boundary ≡ true
singleTypedFrontier = refl
