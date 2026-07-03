module DASHI.Physics.Closure.NSTriadKNGate2AQuotientAwareLiftDefectExpansion where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.String using (_++_)
open import DASHI.Physics.Closure.NSTriadKNGate2AConeRestrictedDefectBudget
  using (NSTriadKNGate2AConeRestrictedDefectBudget;
         canonicalNSTriadKNGate2AConeRestrictedDefectBudget)
open import DASHI.Physics.Closure.NSTriadKNGate2AQuarterMarginLedger
  using (canonicalNSTriadKNGate2AQuarterMarginLedger)
open import DASHI.Physics.Closure.QuarterMarginBase
  using (QuarterMarginModel)
open import DASHI.Physics.Closure.QuotientAwareLiftDefectExpansionBase
  using (QuotientAwareLiftDefectExpansionModel;
         mkQuotientAwareLiftDefectExpansionModel)

------------------------------------------------------------------------
-- Gate 2-A quotient-aware lift-defect expansion.
--
-- This is the next concrete algebraic step after the sampled comparison
-- envelope and before any uniform transport theorem:
--
--   J_abs : seam -> full block carrier for L_abs
--   J_neg : seam -> full block carrier for L_neg
--   ΔJ    = J_neg - J_abs
--
-- For x in the seam carrier, the transported negative numerator expands as
--
--   <J_neg x, L_neg J_neg x>
--   = <J_abs x, L_neg J_abs x>
--   + 2 <ΔJ x, L_neg J_abs x>
--   + <ΔJ x, L_neg ΔJ x>.
--
-- This is the quotient-aware / common-lift comparison seam: if the defect
-- terms are small on the near-extremizer cone, then one can compare the
-- operator-specific Schur lifts through a single reference lift rather than
-- through the dead global worst-case quotient.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data LiftLabel : Set where
  commonReferenceLiftAbs :
    LiftLabel
  negativeOperatorLift :
    LiftLabel
  liftDefectDelta :
    LiftLabel

canonicalLiftLabels : List LiftLabel
canonicalLiftLabels =
  commonReferenceLiftAbs
  ∷ negativeOperatorLift
  ∷ liftDefectDelta
  ∷ []

data DefectExpansionTerm : Set where
  principalReferenceTerm :
    DefectExpansionTerm
  crossDefectTerm :
    DefectExpansionTerm
  pureDefectQuadraticTerm :
    DefectExpansionTerm

canonicalDefectExpansionTerms : List DefectExpansionTerm
canonicalDefectExpansionTerms =
  principalReferenceTerm
  ∷ crossDefectTerm
  ∷ pureDefectQuadraticTerm
  ∷ []

data QuotientAwareTarget : Set where
  compareOperatorSpecificLiftsViaReference :
    QuotientAwareTarget
  boundDefectTermsOnNearExtremizerCone :
    QuotientAwareTarget
  feedDirectionalBudgetInsteadOfGlobalWorstCase :
    QuotientAwareTarget

canonicalTargets : List QuotientAwareTarget
canonicalTargets =
  compareOperatorSpecificLiftsViaReference
  ∷ boundDefectTermsOnNearExtremizerCone
  ∷ feedDirectionalBudgetInsteadOfGlobalWorstCase
  ∷ []

data DefectBudgetComponent : Set where
  principalTermBound :
    DefectBudgetComponent
  crossDefectBound :
    DefectBudgetComponent
  pureDefectBound :
    DefectBudgetComponent
  subcriticalDefectBudget :
    DefectBudgetComponent

canonicalDefectBudgetComponents : List DefectBudgetComponent
canonicalDefectBudgetComponents =
  principalTermBound
  ∷ crossDefectBound
  ∷ pureDefectBound
  ∷ subcriticalDefectBudget
  ∷ []

canonicalReferenceLiftText : String
canonicalReferenceLiftText =
  "Choose the common reference lift J_abs = J_N^abs and write J_neg = J_N^neg = J_abs + DeltaJ."

canonicalNumeratorExpansionText : String
canonicalNumeratorExpansionText =
  "<J_neg x, L_neg J_neg x> = <J_abs x, L_neg J_abs x> + 2 <DeltaJ x, L_neg J_abs x> + <DeltaJ x, L_neg DeltaJ x>."

canonicalDenominatorReferenceText : String
canonicalDenominatorReferenceText =
  "Keep the denominator on the absolute reference side: <J_abs x, L_abs J_abs x> = x^T Schur(L_abs) x, then compare Schur(L_abs) to L_good through the sampled envelope."

canonicalDirectionalClosingText : String
canonicalDirectionalClosingText =
  "The quotient-aware route closes if the cross defect and pure defect terms are small on the Gate 1 near-extremizer cone E_N(epsilon), so that the reference term dominates and the directional ratio remains below the conservative quarter target."

canonicalObstructionText : String
canonicalObstructionText =
  "This expansion is the algebraic reason the raw worst-case quotient can be too lossy: it throws away the decomposition into principal reference transport plus defect corrections."

canonicalDefectBudgetTargetText : String
canonicalDefectBudgetTargetText =
  "| 2 <DeltaJ x, L_neg J_abs x> + <DeltaJ x, L_neg DeltaJ x> | <= eta_defect * <J_abs x, L_abs J_abs x> on E_N(epsilon), with eta_defect small enough to preserve the sampled directional margin."

canonicalPrincipalTermText : String
canonicalPrincipalTermText =
  "Principal reference transport term: compare <J_abs x, L_neg J_abs x> against x^T L_bad x directionally, while keeping the denominator on the absolute reference side."

canonicalCrossDefectText : String
canonicalCrossDefectText =
  "Cross-defect control term: bound 2 <DeltaJ x, L_neg J_abs x> by a cone-restricted defect constant rather than a shell-uniform worst-case quotient."

canonicalPureDefectText : String
canonicalPureDefectText =
  "Pure-defect control term: bound <DeltaJ x, L_neg DeltaJ x> as a genuinely higher-order correction on the near-extremizer cone."

canonicalSubquarterClosureText : String
canonicalSubquarterClosureText =
  "Concrete seam instantiation: set principal ratio = theta_principal, "
  ++ "defect ratio = eta_defect, and transported ratio = theta_principal + "
  ++ "eta_defect. On the common twelfths carrier this is 2 + 1 = 3, so "
  ++ "the transported ratio is exactly the quarter budget."

canonicalQuotientAwareLiftDefectExpansionModel :
  QuotientAwareLiftDefectExpansionModel
canonicalQuotientAwareLiftDefectExpansionModel =
  let
    qm =
      NSTriadKNGate2AQuarterMarginLedger.quarterMarginModel
        canonicalNSTriadKNGate2AQuarterMarginLedger
    open QuarterMarginModel qm
  in
  mkQuotientAwareLiftDefectExpansionModel
    qm
    θ-principal
    η-defect
    (θ-principal + η-defect)
    (refl≤ (θ-principal + η-defect))
    (refl≤ θ-principal)
    (refl≤ η-defect)

open QuotientAwareLiftDefectExpansionModel
  canonicalQuotientAwareLiftDefectExpansionModel

record NSTriadKNGate2AQuotientAwareLiftDefectExpansion : Setω where
  constructor mkNSTriadKNGate2AQuotientAwareLiftDefectExpansion
  field
    coneRestrictedBudget :
      NSTriadKNGate2AConeRestrictedDefectBudget
    coneRestrictedBudgetIsCanonical :
      coneRestrictedBudget ≡
        canonicalNSTriadKNGate2AConeRestrictedDefectBudget

    quotientAwareModel :
      QuotientAwareLiftDefectExpansionModel
    quotientAwareModelIsCanonical :
      quotientAwareModel ≡
        canonicalQuotientAwareLiftDefectExpansionModel

    transportedRatio≤QuarterProof :
      QuotientAwareLiftDefectExpansionModel.transported≤quarter
        quotientAwareModel

    liftLabels : List LiftLabel
    liftLabelsAreCanonical :
      liftLabels ≡ canonicalLiftLabels

    expansionTerms : List DefectExpansionTerm
    expansionTermsAreCanonical :
      expansionTerms ≡ canonicalDefectExpansionTerms

    targets : List QuotientAwareTarget
    targetsAreCanonical :
      targets ≡ canonicalTargets

    defectBudgetComponents : List DefectBudgetComponent
    defectBudgetComponentsAreCanonical :
      defectBudgetComponents ≡ canonicalDefectBudgetComponents

    referenceLiftText : String
    referenceLiftTextIsCanonical :
      referenceLiftText ≡ canonicalReferenceLiftText

    numeratorExpansionText : String
    numeratorExpansionTextIsCanonical :
      numeratorExpansionText ≡ canonicalNumeratorExpansionText

    denominatorReferenceText : String
    denominatorReferenceTextIsCanonical :
      denominatorReferenceText ≡ canonicalDenominatorReferenceText

    directionalClosingText : String
    directionalClosingTextIsCanonical :
      directionalClosingText ≡ canonicalDirectionalClosingText

    obstructionText : String
    obstructionTextIsCanonical :
      obstructionText ≡ canonicalObstructionText

    defectBudgetTargetText : String
    defectBudgetTargetTextIsCanonical :
      defectBudgetTargetText ≡ canonicalDefectBudgetTargetText

    principalTermText : String
    principalTermTextIsCanonical :
      principalTermText ≡ canonicalPrincipalTermText

    crossDefectText : String
    crossDefectTextIsCanonical :
      crossDefectText ≡ canonicalCrossDefectText

    pureDefectText : String
    pureDefectTextIsCanonical :
      pureDefectText ≡ canonicalPureDefectText

    subquarterClosureText : String
    subquarterClosureTextIsCanonical :
      subquarterClosureText ≡ canonicalSubquarterClosureText

    liftLabelCount : Nat
    liftLabelCountIs3 :
      liftLabelCount ≡ 3

    expansionTermCount : Nat
    expansionTermCountIs3 :
      expansionTermCount ≡ 3

    defectBudgetComponentCount : Nat
    defectBudgetComponentCountIs4 :
      defectBudgetComponentCount ≡ 4

    quotientAwareRouteRecorded : Bool
    quotientAwareRouteRecordedIsTrue :
      quotientAwareRouteRecorded ≡ true

    commonReferenceLiftChosen : Bool
    commonReferenceLiftChosenIsTrue :
      commonReferenceLiftChosen ≡ true

    defectExpansionInstalled : Bool
    defectExpansionInstalledIsTrue :
      defectExpansionInstalled ≡ true

    principalCrossQuadraticSplitRecorded : Bool
    principalCrossQuadraticSplitRecordedIsTrue :
      principalCrossQuadraticSplitRecorded ≡ true

    principalTermBounded : Bool
    principalTermBoundedIsFalse :
      principalTermBounded ≡ false

    crossDefectBounded : Bool
    crossDefectBoundedIsFalse :
      crossDefectBounded ≡ false

    pureDefectBounded : Bool
    pureDefectBoundedIsFalse :
      pureDefectBounded ≡ false

    defectBudgetSubcritical : Bool
    defectBudgetSubcriticalIsFalse :
      defectBudgetSubcritical ≡ false

    defectTermsUniformlyBounded : Bool
    defectTermsUniformlyBoundedIsFalse :
      defectTermsUniformlyBounded ≡ false

    quotientAwareTransportProved : Bool
    quotientAwareTransportProvedIsFalse :
      quotientAwareTransportProved ≡ false

    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNGate2AQuotientAwareLiftDefectExpansion public

canonicalNSTriadKNGate2AQuotientAwareLiftDefectExpansion :
  NSTriadKNGate2AQuotientAwareLiftDefectExpansion
canonicalNSTriadKNGate2AQuotientAwareLiftDefectExpansion =
  mkNSTriadKNGate2AQuotientAwareLiftDefectExpansion
    canonicalNSTriadKNGate2AConeRestrictedDefectBudget
    refl
    canonicalQuotientAwareLiftDefectExpansionModel
    refl
    (QuotientAwareLiftDefectExpansionModel.transported≤quarter
      canonicalQuotientAwareLiftDefectExpansionModel)
    canonicalLiftLabels
    refl
    canonicalDefectExpansionTerms
    refl
    canonicalTargets
    refl
    canonicalDefectBudgetComponents
    refl
    canonicalReferenceLiftText
    refl
    canonicalNumeratorExpansionText
    refl
    canonicalDenominatorReferenceText
    refl
    canonicalDirectionalClosingText
    refl
    canonicalObstructionText
    refl
    canonicalDefectBudgetTargetText
    refl
    canonicalPrincipalTermText
    refl
    canonicalCrossDefectText
    refl
    canonicalPureDefectText
    refl
    canonicalSubquarterClosureText
    refl
    3
    refl
    3
    refl
    4
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
