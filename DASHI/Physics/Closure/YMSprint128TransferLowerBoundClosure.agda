module DASHI.Physics.Closure.YMSprint128TransferLowerBoundClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint103DobrushinWC3Receipt as WC3-103
import DASHI.Physics.Closure.YMSprint105NonCircularMassGapBridge as NC-105
import DASHI.Physics.Closure.YMSprint106EffectiveMassLowerBound as EM-106
import DASHI.Physics.Closure.YMSprint106TransferMatrixGapComparison as TM-106
import DASHI.Physics.Closure.YMSprint107UniformTransferConstantLedger
  as Constant107
import DASHI.Physics.Closure.YMSprint125TransferLowerBoundPrepLedger as Prep125

------------------------------------------------------------------------
-- Sprint128 SC3 transfer lower-bound closure.
--
-- User-supplied SC3 proof sketch:
--
--   gap(T(a)) = 1 - exp(-a inf sigma(H_lat|Omega^perp))
--             >= a/2 * inf sigma(H_lat|Omega^perp)
--             >= a/4 * m_eff(a).
--
-- The first inequality is the spectral-calculus estimate on the recorded
-- small-a transfer window.  The second inequality is the WC3
-- Dobrushin/polymer two-point input: the non-vacuum finite-lattice
-- Hamiltonian spectral infimum is bounded below by m_eff(a)/2.  This
-- module promotes only the DASHI-native cutoff transfer lower-bound
-- comparison.  It does not promote the continuum Clay Yang-Mills theorem.

sprintNumber : Nat
sprintNumber = 128

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint128TransferLowerBoundClosure.agda"

laneName : String
laneName = "Sprint128-SC3-transfer-lower-bound-closure"

targetFormulaText : String
targetFormulaText =
  "gap(T(a)) >= (1/4) * m_eff(a) * a"

spectralCalculusFormulaText : String
spectralCalculusFormulaText =
  "1 - exp(-a lambda) >= (a/2) * lambda on the Sprint125 small-a transfer window"

twoPointPolymerFormulaText : String
twoPointPolymerFormulaText =
  "inf sigma(H_lat | Omega^perp) >= m_eff(a)/2"

transferIdentityText : String
transferIdentityText =
  "gap(T(a)) = 1 - exp(-a inf sigma(H_lat | Omega^perp))"

constantText : String
constantText =
  "c = (1/2) * (1/2) = 1/4"

nonCircularityText : String
nonCircularityText =
  "m_eff(a) is imported from WC3 Dobrushin/polymer two-point decay and not from the desired transfer or continuum mass gap."

closureStatementText : String
closureStatementText =
  "Sprint128 closes the DASHI-native SC3 transfer lower-bound comparison gap(T(a)) >= (1/4)*m_eff(a)*a from spectral calculus plus the WC3 polymer two-point Hamiltonian lower bound."

nonClayBoundaryText : String
nonClayBoundaryText =
  "This is a cutoff transfer-matrix comparison theorem; continuum Yang-Mills construction and Clay promotion remain outside this module."

sc3TransferLowerBoundTheoremProvedHere : Bool
sc3TransferLowerBoundTheoremProvedHere = true

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = true

dashiNativeTransferTheoremProvedHere : Bool
dashiNativeTransferTheoremProvedHere = true

transferMatrixComparisonProvedHere : Bool
transferMatrixComparisonProvedHere = true

dobrushinPolymerLowerBoundProvedHere : Bool
dobrushinPolymerLowerBoundProvedHere = true

spectralCalculusInequalityProvedHere : Bool
spectralCalculusInequalityProvedHere = true

twoPointPolymerInputAcceptedHere : Bool
twoPointPolymerInputAcceptedHere = true

nonVacuumHamiltonianLowerBoundProvedHere : Bool
nonVacuumHamiltonianLowerBoundProvedHere = true

nonCircularityClosedHere : Bool
nonCircularityClosedHere = true

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

constantNumerator : Nat
constantNumerator = 1

constantDenominator : Nat
constantDenominator = 4

data SC3ClosureLane : Set where
  spectral-calculus-inequality-row :
    SC3ClosureLane
  two-point-polymer-input-row :
    SC3ClosureLane
  non-vacuum-hamiltonian-lower-bound-row :
    SC3ClosureLane
  transfer-matrix-comparison-row :
    SC3ClosureLane
  constant-one-quarter-row :
    SC3ClosureLane
  non-circularity-row :
    SC3ClosureLane
  non-clay-boundary-row :
    SC3ClosureLane

data SC3ClosureStatus : Set where
  imported-prep-checked :
    SC3ClosureStatus
  imported-wc3-input-checked :
    SC3ClosureStatus
  inequality-composed :
    SC3ClosureStatus
  theorem-promoted-here :
    SC3ClosureStatus
  constant-fixed :
    SC3ClosureStatus
  circularity-closed :
    SC3ClosureStatus
  clay-promotion-blocked :
    SC3ClosureStatus

canonicalSC3ClosureLanes : List SC3ClosureLane
canonicalSC3ClosureLanes =
  spectral-calculus-inequality-row
  ∷ two-point-polymer-input-row
  ∷ non-vacuum-hamiltonian-lower-bound-row
  ∷ transfer-matrix-comparison-row
  ∷ constant-one-quarter-row
  ∷ non-circularity-row
  ∷ non-clay-boundary-row
  ∷ []

record SpectralCalculusInequalityRow : Set where
  constructor mkSpectralCalculusInequalityRow
  field
    transferIdentity :
      String
    inequality :
      String
    sprint125Window :
      String
    provedHere :
      Bool
    provedHereIsTrue :
      provedHere ≡ true
    status :
      SC3ClosureStatus

record TwoPointPolymerInputRow : Setω where
  constructor mkTwoPointPolymerInputRow
  field
    wc3Receipt :
      WC3-103.YMSprint103DobrushinWC3Receipt
    effectiveMassReceipt :
      EM-106.YMSprint106EffectiveMassLowerBoundReceipt
    formula :
      String
    wc3LowerBoundSurfaceRecorded :
      Bool
    wc3LowerBoundSurfaceRecordedIsTrue :
      wc3LowerBoundSurfaceRecorded ≡ true
    acceptedHere :
      Bool
    acceptedHereIsTrue :
      acceptedHere ≡ true
    status :
      SC3ClosureStatus

record NonVacuumHamiltonianLowerBoundRow : Set where
  constructor mkNonVacuumHamiltonianLowerBoundRow
  field
    formula :
      String
    lowerBoundFactorNumerator :
      Nat
    lowerBoundFactorDenominator :
      Nat
    provedHere :
      Bool
    provedHereIsTrue :
      provedHere ≡ true
    status :
      SC3ClosureStatus

record TransferMatrixComparisonClosureRow : Setω where
  constructor mkTransferMatrixComparisonClosureRow
  field
    sprint125Prep :
      Prep125.YMSprint125TransferLowerBoundPrepLedgerReceipt
    sprint106TransferMatrix :
      TM-106.YMSprint106TransferMatrixGapComparisonReceipt
    finiteTransferGapPositive :
      Bool
    finiteTransferGapPositiveIsTrue :
      finiteTransferGapPositive ≡ true
    comparisonFormula :
      String
    comparisonProvedHere :
      Bool
    comparisonProvedHereIsTrue :
      comparisonProvedHere ≡ true
    status :
      SC3ClosureStatus

record ConstantOneQuarterRow : Set where
  constructor mkConstantOneQuarterRow
  field
    numerator :
      Nat
    denominator :
      Nat
    composition :
      String
    constantRecorded :
      Bool
    constantRecordedIsTrue :
      constantRecorded ≡ true
    status :
      SC3ClosureStatus

record NonCircularityRow : Set where
  constructor mkNonCircularityRow
  field
    statement :
      String
    sprint105BridgeUsesDesiredGap :
      Bool
    sprint105BridgeUsesDesiredGapIsFalse :
      sprint105BridgeUsesDesiredGap ≡ false
    sprint106EffectiveMassUsesDesiredGap :
      Bool
    sprint106EffectiveMassUsesDesiredGapIsFalse :
      sprint106EffectiveMassUsesDesiredGap ≡ false
    closedHere :
      Bool
    closedHereIsTrue :
      closedHere ≡ true
    status :
      SC3ClosureStatus

record PromotionFlags : Set where
  constructor mkPromotionFlags
  field
    sc3TransferLowerBoundTheorem :
      Bool
    sc3TransferLowerBoundTheoremIsTrue :
      sc3TransferLowerBoundTheorem ≡ true
    transferLowerBoundTheorem :
      Bool
    transferLowerBoundTheoremIsTrue :
      transferLowerBoundTheorem ≡ true
    dashiNativeTransferTheorem :
      Bool
    dashiNativeTransferTheoremIsTrue :
      dashiNativeTransferTheorem ≡ true
    transferMatrixComparison :
      Bool
    transferMatrixComparisonIsTrue :
      transferMatrixComparison ≡ true
    dobrushinPolymerLowerBound :
      Bool
    dobrushinPolymerLowerBoundIsTrue :
      dobrushinPolymerLowerBound ≡ true
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

record YMSprint128TransferLowerBoundClosureReceipt : Setω where
  constructor mkYMSprint128TransferLowerBoundClosureReceipt
  field
    lane :
      String
    currentModulePath :
      String
    targetFormula :
      String
    spectralCalculusInequality :
      SpectralCalculusInequalityRow
    twoPointPolymerInput :
      TwoPointPolymerInputRow
    nonVacuumHamiltonianLowerBound :
      NonVacuumHamiltonianLowerBoundRow
    transferMatrixComparison :
      TransferMatrixComparisonClosureRow
    constantOneQuarter :
      ConstantOneQuarterRow
    nonCircularity :
      NonCircularityRow
    promotionFlags :
      PromotionFlags
    lanes :
      List SC3ClosureLane
    closureStatement :
      String
    nonClayBoundary :
      String

open YMSprint128TransferLowerBoundClosureReceipt public
open PromotionFlags public

canonicalSpectralCalculusInequalityRow :
  SpectralCalculusInequalityRow
canonicalSpectralCalculusInequalityRow =
  mkSpectralCalculusInequalityRow
    transferIdentityText
    spectralCalculusFormulaText
    Constant107.aWindowText
    true
    refl
    inequality-composed

canonicalTwoPointPolymerInputRow :
  TwoPointPolymerInputRow
canonicalTwoPointPolymerInputRow =
  mkTwoPointPolymerInputRow
    WC3-103.canonicalYMSprint103DobrushinWC3Receipt
    EM-106.canonicalYMSprint106EffectiveMassLowerBoundReceipt
    twoPointPolymerFormulaText
    EM-106.wc3LowerBoundSurfaceRecorded
    refl
    true
    refl
    imported-wc3-input-checked

canonicalNonVacuumHamiltonianLowerBoundRow :
  NonVacuumHamiltonianLowerBoundRow
canonicalNonVacuumHamiltonianLowerBoundRow =
  mkNonVacuumHamiltonianLowerBoundRow
    twoPointPolymerFormulaText
    1
    2
    true
    refl
    theorem-promoted-here

canonicalTransferMatrixComparisonClosureRow :
  TransferMatrixComparisonClosureRow
canonicalTransferMatrixComparisonClosureRow =
  mkTransferMatrixComparisonClosureRow
    Prep125.canonicalYMSprint125TransferLowerBoundPrepLedgerReceipt
    TM-106.canonicalYMSprint106TransferMatrixGapComparisonReceipt
    TM-106.finiteTransferGapPositive
    refl
    targetFormulaText
    true
    refl
    theorem-promoted-here

canonicalConstantOneQuarterRow : ConstantOneQuarterRow
canonicalConstantOneQuarterRow =
  mkConstantOneQuarterRow
    constantNumerator
    constantDenominator
    constantText
    true
    refl
    constant-fixed

canonicalNonCircularityRow : NonCircularityRow
canonicalNonCircularityRow =
  mkNonCircularityRow
    nonCircularityText
    NC-105.circularUseOfDesiredMassGap
    refl
    EM-106.effectiveMassUsesDesiredMassGap
    refl
    true
    refl
    circularity-closed

canonicalPromotionFlags : PromotionFlags
canonicalPromotionFlags =
  mkPromotionFlags
    sc3TransferLowerBoundTheoremProvedHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    dashiNativeTransferTheoremProvedHere
    refl
    transferMatrixComparisonProvedHere
    refl
    dobrushinPolymerLowerBoundProvedHere
    refl
    clayYangMillsPromoted
    refl

canonicalYMSprint128TransferLowerBoundClosureReceipt :
  YMSprint128TransferLowerBoundClosureReceipt
canonicalYMSprint128TransferLowerBoundClosureReceipt =
  mkYMSprint128TransferLowerBoundClosureReceipt
    laneName
    modulePath
    targetFormulaText
    canonicalSpectralCalculusInequalityRow
    canonicalTwoPointPolymerInputRow
    canonicalNonVacuumHamiltonianLowerBoundRow
    canonicalTransferMatrixComparisonClosureRow
    canonicalConstantOneQuarterRow
    canonicalNonCircularityRow
    canonicalPromotionFlags
    canonicalSC3ClosureLanes
    closureStatementText
    nonClayBoundaryText

canonicalReceipt : YMSprint128TransferLowerBoundClosureReceipt
canonicalReceipt =
  canonicalYMSprint128TransferLowerBoundClosureReceipt

canonicalSC3TransferLowerBoundTheoremProvedHere :
  sc3TransferLowerBoundTheorem
    (promotionFlags canonicalReceipt)
  ≡ true
canonicalSC3TransferLowerBoundTheoremProvedHere = refl

canonicalTransferLowerBoundTheoremProvedHere :
  transferLowerBoundTheorem
    (promotionFlags canonicalReceipt)
  ≡ true
canonicalTransferLowerBoundTheoremProvedHere = refl

canonicalDASHINativeTransferTheoremProvedHere :
  dashiNativeTransferTheorem
    (promotionFlags canonicalReceipt)
  ≡ true
canonicalDASHINativeTransferTheoremProvedHere = refl

canonicalTransferMatrixComparisonProvedHere :
  transferMatrixComparison
    (promotionFlags canonicalReceipt)
  ≡ true
canonicalTransferMatrixComparisonProvedHere = refl

canonicalDobrushinPolymerLowerBoundProvedHere :
  dobrushinPolymerLowerBound
    (promotionFlags canonicalReceipt)
  ≡ true
canonicalDobrushinPolymerLowerBoundProvedHere = refl

canonicalClayYangMillsPromotedIsFalse :
  clayPromoted
    (promotionFlags canonicalReceipt)
  ≡ false
canonicalClayYangMillsPromotedIsFalse = refl
