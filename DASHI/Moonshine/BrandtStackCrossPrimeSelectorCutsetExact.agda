module DASHI.Moonshine.BrandtStackCrossPrimeSelectorCutsetExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Record the information threshold learned by comparing the Ogg p=11 model
-- with non-Ogg controls p=37 and p=43 under the SAME source-native stack
-- unweighting prescription.
--
-- Facts now constructed:
--
-- p=11:
--   reciprocal unweighting count 5;
--   positive T2 neighbour system;
--   positive true-identity T2-square relation.
--
-- p=37 (non-Ogg):
--   reciprocal unweighting count 3;
--   source T2 is already an ordinary positive 3-state system;
--   positive true-identity T2-square relation also holds.
--
-- p=43 (non-Ogg):
--   monodromy weights (2,1,1,1);
--   reciprocal unweighting count 7, NOT the misleading weight-sum 5.
--
-- Therefore none of the following can be promoted to an Ogg explanation:
--
--   * existence of stacky automorphism weights;
--   * existence of a finite reciprocal unweighting;
--   * existence of a positive T2 geometry;
--   * positivity of the first unital prime-square residual.
--
-- The next selector must consume strictly richer information: simultaneous
-- multi-prime Hecke action, source-native double-coset generator structure,
-- Frobenius/Fricke interaction, joint spectrum, or an equivalent invariant.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11EichlerDeuringStackUnweightingExact as P11Stack
import DASHI.Moonshine.BrandtStackUnweightingControlsExact as Controls
import DASHI.Moonshine.P37NonOggPositiveHeckeControlExact as P37
import DASHI.Moonshine.P37NonOggPositivePrimeSquareNeighboursExact as P37Square

------------------------------------------------------------------------
-- Exact cross-prime count comparison.
------------------------------------------------------------------------

p11SheetCount : Nat
p11SheetCount = P11Stack.p11UnweightedStateCount

p37SheetCount : Nat
p37SheetCount = Controls.p37UnweightedStateCount

p43SheetCount : Nat
p43SheetCount = Controls.p43UnweightedStateCount

p11SheetCountIsFive : p11SheetCount ≡ 5
p11SheetCountIsFive = refl

p37SheetCountIsThree : p37SheetCount ≡ 3
p37SheetCountIsThree = refl

p43SheetCountIsSeven : p43SheetCount ≡ 7
p43SheetCountIsSeven = refl

p11CountDiffersFromP37 : p11SheetCount ≡ p37SheetCount → ⊥
p11CountDiffersFromP37 ()

p11CountDiffersFromP43 : p11SheetCount ≡ p43SheetCount → ⊥
p11CountDiffersFromP43 ()

------------------------------------------------------------------------
-- Feature-level cutset.  A one-bit selector that sees only whether a positive
-- stack-unweighted T2-square realization exists receives the same input at
-- Ogg p=11 and non-Ogg p=37 and therefore cannot separate them.
------------------------------------------------------------------------

data PositiveT2SquareFeature : Set where
  featurePresent : PositiveT2SquareFeature

p11PositiveFeature : PositiveT2SquareFeature
p11PositiveFeature = featurePresent

p37PositiveFeature : PositiveT2SquareFeature
p37PositiveFeature = featurePresent

featureOnlyClassifierCannotSeparate :
  (classify : PositiveT2SquareFeature → Bool) →
  classify p11PositiveFeature ≡ true →
  classify p37PositiveFeature ≡ false →
  ⊥
featureOnlyClassifierCannotSeparate classify p11True p37False
  rewrite p11True
  = λ () → p37False

------------------------------------------------------------------------
-- A useful positive result from the controls: the reciprocal sheet COUNT is
-- already richer than the mere existence feature for the three tested levels.
-- It is deliberately NOT promoted to a global Ogg selector; two controls are
-- nowhere near enough to support that theorem.
------------------------------------------------------------------------

record CrossPrimeStackSignature : Set where
  constructor stackSignature
  field
    characteristic : Nat
    classCount : Nat
    sheetCount : Nat
    positiveT2SquareKnown : Bool

open CrossPrimeStackSignature public

p11Signature : CrossPrimeStackSignature
p11Signature = stackSignature 11 2 5 true

p37Signature : CrossPrimeStackSignature
p37Signature = stackSignature 37 3 3 true

p43Signature : CrossPrimeStackSignature
p43Signature = stackSignature 43 4 7 false

record BrandtStackSelectorCutsetBoundary : Set where
  field
    reciprocalUnweightingTestedAcrossControls : Bool
    reciprocalUnweightingTestedAcrossControlsIsTrue :
      reciprocalUnweightingTestedAcrossControls ≡ true

    positiveT2SquareFeatureRefutedAsOggSelector : Bool
    positiveT2SquareFeatureRefutedAsOggSelectorIsTrue :
      positiveT2SquareFeatureRefutedAsOggSelector ≡ true

    sheetCountPromotedToGlobalOggSelector : Bool
    sheetCountPromotedToGlobalOggSelectorIsFalse :
      sheetCountPromotedToGlobalOggSelector ≡ false

    jointHeckeFrickeFrobeniusSelectorConstructedHere : Bool
    jointHeckeFrickeFrobeniusSelectorConstructedHereIsFalse :
      jointHeckeFrickeFrobeniusSelectorConstructedHere ≡ false

canonicalBrandtStackSelectorCutsetBoundary :
  BrandtStackSelectorCutsetBoundary
canonicalBrandtStackSelectorCutsetBoundary =
  record
    { reciprocalUnweightingTestedAcrossControls = true
    ; reciprocalUnweightingTestedAcrossControlsIsTrue = refl
    ; positiveT2SquareFeatureRefutedAsOggSelector = true
    ; positiveT2SquareFeatureRefutedAsOggSelectorIsTrue = refl
    ; sheetCountPromotedToGlobalOggSelector = false
    ; sheetCountPromotedToGlobalOggSelectorIsFalse = refl
    ; jointHeckeFrickeFrobeniusSelectorConstructedHere = false
    ; jointHeckeFrickeFrobeniusSelectorConstructedHereIsFalse = refl
    }
