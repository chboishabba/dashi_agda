module DASHI.Foundations.SurrealCompactificationTailBoundBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Algebra.Trit using (Trit)
import DASHI.Foundations.SurrealCompactification as SC
import DASHI.Foundations.SurrealCompactificationIntake as Intake
import DASHI.Foundations.SurrealCompactificationRationalBridge as RationalBridge
import DASHI.Foundations.CarrierPromotionBoundaryCore as CarrierCore

------------------------------------------------------------------------
-- Exact fail-closed analytic law shapes.
--
-- These records expose the compactification/tail-bound bridge requested by
-- downstream modules.  They connect only checked finite towers, symbolic
-- rational approximants, and the intake authority records.  The analytic
-- geometric-series and kappa inequalities remain fail-closed authority slots.

record GeometricSeriesTailLawShape (n : Nat) : Set₁ where
  constructor geometric-series-tail
  field
    tailStart :
      Nat

    tailStartIsN :
      tailStart ≡ n

    tailFormula :
      String

    tailFormulaIsCanonical :
      tailFormula ≡ "sum_{i>=n} 3^-i"

    tailGauge :
      Intake.SymbolicGauge

    tailGaugeIsThreeMinusN :
      tailGauge ≡ Intake.threeToMinus n

    tailBoundIntake :
      Intake.TailBoundIntake n

    tailBoundIntakeIsCanonical :
      tailBoundIntake ≡ Intake.canonicalTailBoundIntake n

    finiteTowerCarrier :
      Nat →
      Set

    finiteTowerCarrierIsInternal :
      finiteTowerCarrier ≡ SC.FiniteTritTower

    symbolicRationalCarrier :
      Set

    symbolicRationalCarrierIsInternal :
      symbolicRationalCarrier
      ≡
      RationalBridge.SymbolicRationalApproximation

    rationalBridge :
      RationalBridge.FiniteTritTowerSymbolicRationalBridge

    rationalBridgeIsCanonical :
      rationalBridge
      ≡
      RationalBridge.canonicalFiniteTritTowerSymbolicRationalBridge

    analyticProofStatus :
      Intake.IntakeCheckStatus

    analyticProofStatusIsFailClosed :
      analyticProofStatus ≡ Intake.externalAuthorityRequiredFailClosed

    analyticTailBoundProvedHere :
      Bool

    analyticTailBoundProvedHereIsFalse :
      analyticTailBoundProvedHere ≡ false

    analyticTailBoundPromoted :
      Bool

    analyticTailBoundPromotedIsFalse :
      analyticTailBoundPromoted ≡ false

open GeometricSeriesTailLawShape public

geometric-series-tail-law :
  (n : Nat) →
  GeometricSeriesTailLawShape n
geometric-series-tail-law n =
  geometric-series-tail
    n
    refl
    "sum_{i>=n} 3^-i"
    refl
    (Intake.threeToMinus n)
    refl
    (Intake.canonicalTailBoundIntake n)
    refl
    SC.FiniteTritTower
    refl
    RationalBridge.SymbolicRationalApproximation
    refl
    RationalBridge.canonicalFiniteTritTowerSymbolicRationalBridge
    refl
    Intake.externalAuthorityRequiredFailClosed
    refl
    false
    refl
    false
    refl

record KappaTailBoundLawShape (n k : Nat) : Set₁ where
  constructor kappaTailBound
  field
    geometricTail :
      GeometricSeriesTailLawShape n

    geometricTailIsCanonical :
      geometricTail ≡ geometric-series-tail-law n

    truncationKappaIntake :
      Intake.TruncationKappaIntake k

    truncationKappaIntakeIsCanonical :
      truncationKappaIntake ≡ Intake.canonicalTruncationKappaIntake k

    kappaReference :
      Intake.KappaShape

    kappaReferenceIsAtK :
      kappaReference ≡ Intake.kappaOfDepth k

    exactCheckedRationalBridgeFields :
      Intake.ExactCheckedRationalBridgeFields n n k

    exactCheckedRationalBridgeFieldsAreCanonical :
      exactCheckedRationalBridgeFields
      ≡
      Intake.canonicalExactCheckedRationalBridgeFields n n k

    internalTruncationSurface :
      SC.InternalBoundedTruncationSurface

    internalTruncationSurfaceIsCanonical :
      internalTruncationSurface
      ≡
      SC.canonicalInternalBoundedTruncationSurface

    compactificationIntake :
      Intake.SurrealCompactificationIntakeContract

    compactificationIntakeIsCanonical :
      compactificationIntake
      ≡
      Intake.canonicalSurrealCompactificationIntakeContract

    noPromotionFlags :
      Intake.NoPromotionFlags

    noPromotionFlagsAreCanonical :
      noPromotionFlags ≡ Intake.canonicalNoPromotionFlags

    kappaAnalyticProofStatus :
      Intake.IntakeCheckStatus

    kappaAnalyticProofStatusIsFailClosed :
      kappaAnalyticProofStatus
      ≡
      Intake.externalAuthorityRequiredFailClosed

    kappaTailBoundProvedHere :
      Bool

    kappaTailBoundProvedHereIsFalse :
      kappaTailBoundProvedHere ≡ false

    kappaTailBoundPromoted :
      Bool

    kappaTailBoundPromotedIsFalse :
      kappaTailBoundPromoted ≡ false

open KappaTailBoundLawShape public

kappaTailBound-law :
  (n k : Nat) →
  KappaTailBoundLawShape n k
kappaTailBound-law n k =
  kappaTailBound
    (geometric-series-tail-law n)
    refl
    (Intake.canonicalTruncationKappaIntake k)
    refl
    (Intake.kappaOfDepth k)
    refl
    (Intake.canonicalExactCheckedRationalBridgeFields n n k)
    refl
    SC.canonicalInternalBoundedTruncationSurface
    refl
    Intake.canonicalSurrealCompactificationIntakeContract
    refl
    Intake.canonicalNoPromotionFlags
    refl
    Intake.externalAuthorityRequiredFailClosed
    refl
    false
    refl
    false
    refl

record CompactificationTailBoundBridgeSurface (n k : Nat) : Set₁ where
  field
    tailBoundPromotionCore :
      CarrierCore.CarrierPromotionReceipt

    tailBoundPromotionCoreIsCanonical :
      tailBoundPromotionCore
      ≡
      CarrierCore.canonicalTailBoundPromotionReceipt

    tailBoundPromotionCoreProvedFalse :
      CarrierCore.analyticTailBoundProvedHere
        (CarrierCore.boundary tailBoundPromotionCore)
      ≡
      false

    geometricSeriesTail :
      GeometricSeriesTailLawShape n

    geometricSeriesTailIsCanonical :
      geometricSeriesTail ≡ geometric-series-tail-law n

    kappaTailBoundSurface :
      KappaTailBoundLawShape n k

    kappaTailBoundSurfaceIsCanonical :
      kappaTailBoundSurface ≡ kappaTailBound-law n k

    rationalBridge :
      RationalBridge.FiniteTritTowerSymbolicRationalBridge

    rationalBridgeIsCanonical :
      rationalBridge
      ≡
      RationalBridge.canonicalFiniteTritTowerSymbolicRationalBridge

    compactificationSurface :
      SC.InternalBoundedTruncationSurface

    compactificationSurfaceIsCanonical :
      compactificationSurface
      ≡
      SC.canonicalInternalBoundedTruncationSurface

    intakeContract :
      Intake.SurrealCompactificationIntakeContract

    intakeContractIsCanonical :
      intakeContract
      ≡
      Intake.canonicalSurrealCompactificationIntakeContract

    allAnalyticProofsFailClosed :
      Bool

    allAnalyticProofsFailClosedIsTrue :
      allAnalyticProofsFailClosed ≡ true

    anyAnalyticProofPromotedHere :
      Bool

    anyAnalyticProofPromotedHereIsFalse :
      anyAnalyticProofPromotedHere ≡ false

open CompactificationTailBoundBridgeSurface public

canonicalCompactificationTailBoundBridgeSurface :
  (n k : Nat) →
  CompactificationTailBoundBridgeSurface n k
canonicalCompactificationTailBoundBridgeSurface n k =
  record
    { tailBoundPromotionCore =
        CarrierCore.canonicalTailBoundPromotionReceipt
    ; tailBoundPromotionCoreIsCanonical =
        refl
    ; tailBoundPromotionCoreProvedFalse =
        refl
    ; geometricSeriesTail =
        geometric-series-tail-law n
    ; geometricSeriesTailIsCanonical =
        refl
    ; kappaTailBoundSurface =
        kappaTailBound-law n k
    ; kappaTailBoundSurfaceIsCanonical =
        refl
    ; rationalBridge =
        RationalBridge.canonicalFiniteTritTowerSymbolicRationalBridge
    ; rationalBridgeIsCanonical =
        refl
    ; compactificationSurface =
        SC.canonicalInternalBoundedTruncationSurface
    ; compactificationSurfaceIsCanonical =
        refl
    ; intakeContract =
        Intake.canonicalSurrealCompactificationIntakeContract
    ; intakeContractIsCanonical =
        refl
    ; allAnalyticProofsFailClosed =
        true
    ; allAnalyticProofsFailClosedIsTrue =
        refl
    ; anyAnalyticProofPromotedHere =
        false
    ; anyAnalyticProofPromotedHereIsFalse =
        refl
    }

canonicalGeometricSeriesTailFailsClosed :
  (n : Nat) →
  analyticProofStatus (geometric-series-tail-law n)
  ≡
  Intake.externalAuthorityRequiredFailClosed
canonicalGeometricSeriesTailFailsClosed n =
  refl

------------------------------------------------------------------------
-- Checked kappa and truncation receipts.
--
-- The following surface is intentionally structural.  It witnesses that a
-- finite kappa-depth tower can be truncated by the internal
-- FiniteTritTower/truncateTower machinery and that the resulting tower has
-- the indexed target depth.  It does not prove a numerical tail inequality.

kappa :
  Nat →
  Intake.KappaShape
kappa =
  Intake.kappaOfDepth

kappa-is-depth :
  (depth : Nat) →
  kappa depth ≡ Intake.kappaOfDepth depth
kappa-is-depth depth =
  refl

kappa9 :
  Intake.KappaShape
kappa9 =
  kappa SC.nine

kappa9-is-depth9 :
  kappa9 ≡ Intake.kappaOfDepth SC.nine
kappa9-is-depth9 =
  refl

record TailSumBoundShape (tailStart kappaDepth : Nat) : Set₁ where
  constructor tailSumBoundShape
  field
    tailSumStart :
      Nat

    tailSumStartIsIndex :
      tailSumStart ≡ tailStart

    tailSumKappaDepth :
      Nat

    tailSumKappaDepthIsIndex :
      tailSumKappaDepth ≡ kappaDepth

    tailSumFormula :
      String

    tailSumFormulaIsCanonical :
      tailSumFormula ≡ "sum_{i>=n} 3^-i <= kappa(k)"

    tailSumShape :
      Intake.TailBoundShape

    tailSumShapeIsFromStart :
      tailSumShape ≡ Intake.ternaryTailFrom tailStart

    tailSumKappa :
      Intake.KappaShape

    tailSumKappaIsCanonical :
      tailSumKappa ≡ kappa kappaDepth

    tailSumGauge :
      Intake.SymbolicGauge

    tailSumGaugeIsThreeMinusStart :
      tailSumGauge ≡ Intake.threeToMinus tailStart

    tailSumIntake :
      Intake.TailBoundIntake tailStart

    tailSumIntakeIsCanonical :
      tailSumIntake ≡ Intake.canonicalTailBoundIntake tailStart

    tailSumGeometricLaw :
      GeometricSeriesTailLawShape tailStart

    tailSumGeometricLawIsCanonical :
      tailSumGeometricLaw ≡ geometric-series-tail-law tailStart

    tailSumAnalyticStatus :
      Intake.IntakeCheckStatus

    tailSumAnalyticStatusIsFailClosed :
      tailSumAnalyticStatus ≡ Intake.externalAuthorityRequiredFailClosed

    tailSumAnalyticInequalityProvedHere :
      Bool

    tailSumAnalyticInequalityProvedHereIsFalse :
      tailSumAnalyticInequalityProvedHere ≡ false

open TailSumBoundShape public

tailSum-bound-shape :
  (tailStart kappaDepth : Nat) →
  TailSumBoundShape tailStart kappaDepth
tailSum-bound-shape tailStart kappaDepth =
  tailSumBoundShape
    tailStart
    refl
    kappaDepth
    refl
    "sum_{i>=n} 3^-i <= kappa(k)"
    refl
    (Intake.ternaryTailFrom tailStart)
    refl
    (kappa kappaDepth)
    refl
    (Intake.threeToMinus tailStart)
    refl
    (Intake.canonicalTailBoundIntake tailStart)
    refl
    (geometric-series-tail-law tailStart)
    refl
    Intake.externalAuthorityRequiredFailClosed
    refl
    false
    refl

tailSum-bound :
  (tailStart kappaDepth : Nat) →
  TailSumBoundShape tailStart kappaDepth
tailSum-bound =
  tailSum-bound-shape

data TruncateTowerInductionReceipt :
  {target source : Nat} →
  SC._≤_ target source →
  SC.FiniteTritTower source →
  Set where
  truncateTower-zero-receipt :
    {source : Nat} →
    (tower : SC.FiniteTritTower source) →
    TruncateTowerInductionReceipt SC.z≤n tower

  truncateTower-suc-receipt :
    {target source : Nat} →
    {target≤source : SC._≤_ target source} →
    (tower : SC.FiniteTritTower source) →
    (trit : Trit) →
    TruncateTowerInductionReceipt target≤source tower →
    TruncateTowerInductionReceipt
      (SC.s≤s target≤source)
      (SC.extendTower tower trit)

truncateTower-induction :
  {target source : Nat} →
  (target≤source : SC._≤_ target source) →
  (tower : SC.FiniteTritTower source) →
  TruncateTowerInductionReceipt target≤source tower
truncateTower-induction SC.z≤n tower =
  truncateTower-zero-receipt tower
truncateTower-induction (SC.s≤s target≤source) (SC.extendTower tower trit) =
  truncateTower-suc-receipt
    tower
    trit
    (truncateTower-induction target≤source tower)

truncateTower-induction-result :
  {target source : Nat} →
  {target≤source : SC._≤_ target source} →
  {tower : SC.FiniteTritTower source} →
  TruncateTowerInductionReceipt target≤source tower →
  SC.FiniteTritTower target
truncateTower-induction-result (truncateTower-zero-receipt tower) =
  SC.emptyTower
truncateTower-induction-result
  (truncateTower-suc-receipt tower trit receipt) =
  SC.extendTower (truncateTower-induction-result receipt) trit

truncateTower-induction-result-is-internal :
  {target source : Nat} →
  {target≤source : SC._≤_ target source} →
  {tower : SC.FiniteTritTower source} →
  (receipt : TruncateTowerInductionReceipt target≤source tower) →
  truncateTower-induction-result receipt
  ≡
  SC.truncateTower target≤source tower
truncateTower-induction-result-is-internal
  (truncateTower-zero-receipt tower) =
  refl
truncateTower-induction-result-is-internal
  (truncateTower-suc-receipt tower trit receipt) =
  SC.cong
    (λ lowerTower → SC.extendTower lowerTower trit)
    (truncateTower-induction-result-is-internal receipt)

record KappaTailBoundStructuralReceipt
  {target source : Nat}
  (target≤source : SC._≤_ target source)
  (tower : SC.FiniteTritTower source) :
  Set₁ where
  constructor kappaTailBoundStructuralReceipt
  field
    receiptTargetDepth :
      Nat

    receiptTargetDepthIsIndex :
      receiptTargetDepth ≡ target

    receiptSourceDepth :
      Nat

    receiptSourceDepthIsIndex :
      receiptSourceDepth ≡ source

    receiptKappa :
      Intake.KappaShape

    receiptKappaIsSourceDepth :
      receiptKappa ≡ kappa source

    receiptTailSumBoundShape :
      TailSumBoundShape target source

    receiptTailSumBoundShapeIsCanonical :
      receiptTailSumBoundShape ≡ tailSum-bound target source

    receiptInduction :
      TruncateTowerInductionReceipt target≤source tower

    receiptInductionResult :
      SC.FiniteTritTower target

    receiptInductionResultIsInternal :
      receiptInductionResult ≡ SC.truncateTower target≤source tower

    receiptTruncatedTower :
      SC.FiniteTritTower target

    receiptTruncatedTowerIsInternal :
      receiptTruncatedTower ≡ SC.truncateTower target≤source tower

    receiptTruncatedTowerDepth :
      SC.towerDepthValue receiptTruncatedTower ≡ target

    receiptTruncatedTowerVecCompatible :
      SC.towerToVec receiptTruncatedTower
      ≡
      SC.truncateVec target≤source (SC.towerToVec tower)

    receiptSourceBoundedAtKappa :
      SC.BoundedFiniteTritTower source

    receiptSourceBoundedAtKappaIsSource :
      SC.actualDepth receiptSourceBoundedAtKappa ≡ source

    receiptTargetBoundedAtKappa :
      SC.BoundedFiniteTritTower source

    receiptTargetBoundedAtKappaDepth :
      SC.towerDepthValue (SC.boundedTower receiptTargetBoundedAtKappa)
      ≡
      target

    receiptAnalyticTailBoundStatus :
      Intake.IntakeCheckStatus

    receiptAnalyticTailBoundStatusIsFailClosed :
      receiptAnalyticTailBoundStatus
      ≡
      Intake.externalAuthorityRequiredFailClosed

    receiptAnalyticTailBoundProvedHere :
      Bool

    receiptAnalyticTailBoundProvedHereIsFalse :
      receiptAnalyticTailBoundProvedHere ≡ false

    receiptPromotesAnalyticBound :
      Bool

    receiptPromotesAnalyticBoundIsFalse :
      receiptPromotesAnalyticBound ≡ false

open KappaTailBoundStructuralReceipt public

kappaTailBound-receipt :
  {target source : Nat} →
  (target≤source : SC._≤_ target source) →
  (tower : SC.FiniteTritTower source) →
  KappaTailBoundStructuralReceipt target≤source tower
kappaTailBound-receipt {target} {source} target≤source tower =
  kappaTailBoundStructuralReceipt
    target
    refl
    source
    refl
    (kappa source)
    refl
    (tailSum-bound target source)
    refl
    (truncateTower-induction target≤source tower)
    (truncateTower-induction-result
      (truncateTower-induction target≤source tower))
    (truncateTower-induction-result-is-internal
      (truncateTower-induction target≤source tower))
    (SC.truncateTower target≤source tower)
    refl
    (SC.truncateTower-depth target≤source tower)
    (SC.truncateTower-vec-compatible target≤source tower)
    (SC.boundedFiniteTritTower source (SC.≤-refl source) tower)
    refl
    (SC.boundedFiniteTritTower
      target
      target≤source
      (SC.truncateTower target≤source tower))
    (SC.truncateTower-depth target≤source tower)
    Intake.externalAuthorityRequiredFailClosed
    refl
    false
    refl
    false
    refl

record Kappa9TailBoundReceipt
  {kappaDepth : Nat}
  (nine≤kappa : SC._≤_ SC.nine kappaDepth)
  (tower : SC.FiniteTritTower kappaDepth) :
  Set₁ where
  constructor kappa9TailBoundReceipt
  field
    kappa9ReceiptSourceDepth :
      Nat

    kappa9ReceiptSourceDepthIsIndex :
      kappa9ReceiptSourceDepth ≡ kappaDepth

    kappa9ReceiptSourceKappa :
      Intake.KappaShape

    kappa9ReceiptSourceKappaIsCanonical :
      kappa9ReceiptSourceKappa ≡ kappa kappaDepth

    kappa9ReceiptTargetKappa :
      Intake.KappaShape

    kappa9ReceiptTargetKappaIsCanonical :
      kappa9ReceiptTargetKappa ≡ kappa9

    kappa9ReceiptTailSumBound :
      TailSumBoundShape SC.nine kappaDepth

    kappa9ReceiptTailSumBoundIsCanonical :
      kappa9ReceiptTailSumBound ≡ tailSum-bound SC.nine kappaDepth

    kappa9ReceiptDepth9 :
      SC.KappaToDepth9Receipt

    kappa9ReceiptDepth9IsCanonical :
      kappa9ReceiptDepth9 ≡ SC.canonicalKappaToDepth9Receipt nine≤kappa tower

    kappa9ReceiptStructural :
      KappaTailBoundStructuralReceipt nine≤kappa tower

    kappa9ReceiptStructuralIsCanonical :
      kappa9ReceiptStructural ≡ kappaTailBound-receipt nine≤kappa tower

    kappa9ReceiptTruncationsAgree :
      receiptTruncatedTower kappa9ReceiptStructural
      ≡
      SC.depth9Tower kappa9ReceiptDepth9

    kappa9ReceiptDepthChecked :
      SC.towerDepthValue (receiptTruncatedTower kappa9ReceiptStructural)
      ≡
      SC.nine

    kappa9ReceiptVecCompatible :
      SC.towerToVec (receiptTruncatedTower kappa9ReceiptStructural)
      ≡
      SC.kappaToDepth9Vec nine≤kappa (SC.towerToVec tower)

    kappa9AnalyticTailBoundStatus :
      Intake.IntakeCheckStatus

    kappa9AnalyticTailBoundStatusIsFailClosed :
      kappa9AnalyticTailBoundStatus
      ≡
      Intake.externalAuthorityRequiredFailClosed

    kappa9AnalyticTailBoundProvedHere :
      Bool

    kappa9AnalyticTailBoundProvedHereIsFalse :
      kappa9AnalyticTailBoundProvedHere ≡ false

open Kappa9TailBoundReceipt public

canonicalKappa9TailBoundReceipt :
  {kappaDepth : Nat} →
  (nine≤kappa : SC._≤_ SC.nine kappaDepth) →
  (tower : SC.FiniteTritTower kappaDepth) →
  Kappa9TailBoundReceipt nine≤kappa tower
canonicalKappa9TailBoundReceipt {kappaDepth} nine≤kappa tower =
  kappa9TailBoundReceipt
    kappaDepth
    refl
    (kappa kappaDepth)
    refl
    kappa9
    refl
    (tailSum-bound SC.nine kappaDepth)
    refl
    (SC.canonicalKappaToDepth9Receipt nine≤kappa tower)
    refl
    (kappaTailBound-receipt nine≤kappa tower)
    refl
    refl
    (SC.kappaToDepth9-depth nine≤kappa tower)
    (SC.kappaToDepth9-vec-compatible nine≤kappa tower)
    Intake.externalAuthorityRequiredFailClosed
    refl
    false
    refl

tailSum-bound-fails-closed :
  (tailStart kappaDepth : Nat) →
  tailSumAnalyticStatus (tailSum-bound tailStart kappaDepth)
  ≡
  Intake.externalAuthorityRequiredFailClosed
tailSum-bound-fails-closed tailStart kappaDepth =
  refl

kappaTailBound-receipt-depth :
  {target source : Nat} →
  (target≤source : SC._≤_ target source) →
  (tower : SC.FiniteTritTower source) →
  SC.towerDepthValue
    (receiptTruncatedTower (kappaTailBound-receipt target≤source tower))
  ≡
  target
kappaTailBound-receipt-depth target≤source tower =
  SC.truncateTower-depth target≤source tower

kappaTailBound-receipt-fails-closed :
  {target source : Nat} →
  (target≤source : SC._≤_ target source) →
  (tower : SC.FiniteTritTower source) →
  receiptAnalyticTailBoundStatus
    (kappaTailBound-receipt target≤source tower)
  ≡
  Intake.externalAuthorityRequiredFailClosed
kappaTailBound-receipt-fails-closed target≤source tower =
  refl

kappa9TailBound-receipt-depth :
  {kappaDepth : Nat} →
  (nine≤kappa : SC._≤_ SC.nine kappaDepth) →
  (tower : SC.FiniteTritTower kappaDepth) →
  SC.towerDepthValue
    (receiptTruncatedTower
      (kappa9ReceiptStructural
        (canonicalKappa9TailBoundReceipt nine≤kappa tower)))
  ≡
  SC.nine
kappa9TailBound-receipt-depth nine≤kappa tower =
  SC.kappaToDepth9-depth nine≤kappa tower

kappa9TailBound-receipt-fails-closed :
  {kappaDepth : Nat} →
  (nine≤kappa : SC._≤_ SC.nine kappaDepth) →
  (tower : SC.FiniteTritTower kappaDepth) →
  kappa9AnalyticTailBoundStatus
    (canonicalKappa9TailBoundReceipt nine≤kappa tower)
  ≡
  Intake.externalAuthorityRequiredFailClosed
kappa9TailBound-receipt-fails-closed nine≤kappa tower =
  refl

canonicalKappaTailBoundFailsClosed :
  (n k : Nat) →
  kappaAnalyticProofStatus (kappaTailBound-law n k)
  ≡
  Intake.externalAuthorityRequiredFailClosed
canonicalKappaTailBoundFailsClosed n k =
  refl

canonicalKappaTailBoundDoesNotPromote :
  (n k : Nat) →
  kappaTailBoundPromoted (kappaTailBound-law n k) ≡ false
canonicalKappaTailBoundDoesNotPromote n k =
  refl
