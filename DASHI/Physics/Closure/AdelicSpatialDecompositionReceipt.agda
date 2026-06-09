module DASHI.Physics.Closure.AdelicSpatialDecompositionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Adelic spatial decomposition receipt.
--
-- This receipt records the boundary/spatial bookkeeping split for the
-- Shimura-tower geometry into its archimedean and non-archimedean factors.
-- It does not promote any Clay/YM, terminal, or analytic closure claim.

data AdelicSpatialDecompositionStatus : Set where
  adelicSpatialDecompositionRecordedNoPromotion :
    AdelicSpatialDecompositionStatus

data ArchimedeanModularCurve : Set where
  X0-3^k :
    ArchimedeanModularCurve

  X0-4^k :
    ArchimedeanModularCurve

  X0-7^k :
    ArchimedeanModularCurve

canonicalArchimedeanModularCurves :
  List ArchimedeanModularCurve
canonicalArchimedeanModularCurves =
  X0-3^k
  ∷ X0-4^k
  ∷ X0-7^k
  ∷ []

data ArchimedeanMetricComponent : Set where
  realHyperbolicMetric :
    ArchimedeanMetricComponent

  H3WithHyperbolicMetric :
    ArchimedeanMetricComponent

canonicalArchimedeanMetricComponents :
  List ArchimedeanMetricComponent
canonicalArchimedeanMetricComponents =
  realHyperbolicMetric
  ∷ H3WithHyperbolicMetric
  ∷ []

data ArchimedeanBoundaryComponent : Set where
  P1-R :
    ArchimedeanBoundaryComponent

canonicalArchimedeanBoundaryComponents :
  List ArchimedeanBoundaryComponent
canonicalArchimedeanBoundaryComponents =
  P1-R
  ∷ []

data NonArchimedeanTreeComponent : Set where
  T3 :
    NonArchimedeanTreeComponent

  T2 :
    NonArchimedeanTreeComponent

  T7 :
    NonArchimedeanTreeComponent

canonicalNonArchimedeanTreeComponents :
  List NonArchimedeanTreeComponent
canonicalNonArchimedeanTreeComponents =
  T3
  ∷ T2
  ∷ T7
  ∷ []

data NonArchimedeanBoundaryComponent : Set where
  P1-Q3 :
    NonArchimedeanBoundaryComponent

  P1-Q2 :
    NonArchimedeanBoundaryComponent

  P1-Q7 :
    NonArchimedeanBoundaryComponent

canonicalNonArchimedeanBoundaryComponents :
  List NonArchimedeanBoundaryComponent
canonicalNonArchimedeanBoundaryComponents =
  P1-Q3
  ∷ P1-Q2
  ∷ P1-Q7
  ∷ []

data AdelicSpatialDecompositionPromotion : Set where

adelicSpatialDecompositionPromotionImpossibleHere :
  AdelicSpatialDecompositionPromotion →
  ⊥
adelicSpatialDecompositionPromotionImpossibleHere ()

adelicSpatialDecompositionStatement : String
adelicSpatialDecompositionStatement =
  "Adelic Shimura tower spatial geometry decomposes as archimedean modular-curve/hyperbolic geometry times p-adic Bruhat-Tits tree geometry; this is bookkeeping only and introduces no Clay/YM or terminal promotion."

record AdelicSpatialDecompositionReceipt : Set where
  field
    status :
      AdelicSpatialDecompositionStatus

    decompositionLabel :
      String

    archimedeanFactorLabel :
      String

    archimedeanModularCurves :
      List ArchimedeanModularCurve

    archimedeanModularCurvesAreCanonical :
      archimedeanModularCurves ≡ canonicalArchimedeanModularCurves

    archimedeanMetricComponents :
      List ArchimedeanMetricComponent

    archimedeanMetricComponentsAreCanonical :
      archimedeanMetricComponents ≡ canonicalArchimedeanMetricComponents

    archimedeanBoundaryComponents :
      List ArchimedeanBoundaryComponent

    archimedeanBoundaryComponentsAreCanonical :
      archimedeanBoundaryComponents ≡ canonicalArchimedeanBoundaryComponents

    nonArchimedeanFactorLabel :
      String

    nonArchimedeanTreeComponents :
      List NonArchimedeanTreeComponent

    nonArchimedeanTreeComponentsAreCanonical :
      nonArchimedeanTreeComponents ≡ canonicalNonArchimedeanTreeComponents

    nonArchimedeanBoundaryComponents :
      List NonArchimedeanBoundaryComponent

    nonArchimedeanBoundaryComponentsAreCanonical :
      nonArchimedeanBoundaryComponents
      ≡
      canonicalNonArchimedeanBoundaryComponents

    pAdicBoundaryProductLabel :
      String

    pAdicBoundaryIsUltrametric :
      Bool

    pAdicBoundaryIsUltrametricIsTrue :
      pAdicBoundaryIsUltrametric ≡ true

    archimedeanBoundaryIsNotUltrametric :
      Bool

    archimedeanBoundaryIsNotUltrametricIsTrue :
      archimedeanBoundaryIsNotUltrametric ≡ true

    geometryBookkeepingOnly :
      Bool

    geometryBookkeepingOnlyIsTrue :
      geometryBookkeepingOnly ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalPromotionIntroduced :
      Bool

    terminalPromotionIntroducedIsFalse :
      terminalPromotionIntroduced ≡ false

    promotionFlags :
      List AdelicSpatialDecompositionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ adelicSpatialDecompositionStatement

    receiptBoundary :
      List String

open AdelicSpatialDecompositionReceipt public

canonicalAdelicSpatialDecompositionReceipt :
  AdelicSpatialDecompositionReceipt
canonicalAdelicSpatialDecompositionReceipt =
  record
    { status =
        adelicSpatialDecompositionRecordedNoPromotion
    ; decompositionLabel =
        "Shimura tower boundary/spatial geometry = archimedean factor x p-adic factor"
    ; archimedeanFactorLabel =
        "X0(3^k), X0(4^k), X0(7^k) with real hyperbolic metric; boundary P1(R); H3WithHyperbolicMetric"
    ; archimedeanModularCurves =
        canonicalArchimedeanModularCurves
    ; archimedeanModularCurvesAreCanonical =
        refl
    ; archimedeanMetricComponents =
        canonicalArchimedeanMetricComponents
    ; archimedeanMetricComponentsAreCanonical =
        refl
    ; archimedeanBoundaryComponents =
        canonicalArchimedeanBoundaryComponents
    ; archimedeanBoundaryComponentsAreCanonical =
        refl
    ; nonArchimedeanFactorLabel =
        "Bruhat-Tits trees T3, T2, T7"
    ; nonArchimedeanTreeComponents =
        canonicalNonArchimedeanTreeComponents
    ; nonArchimedeanTreeComponentsAreCanonical =
        refl
    ; nonArchimedeanBoundaryComponents =
        canonicalNonArchimedeanBoundaryComponents
    ; nonArchimedeanBoundaryComponentsAreCanonical =
        refl
    ; pAdicBoundaryProductLabel =
        "P1(Q3) x P1(Q2) x P1(Q7)"
    ; pAdicBoundaryIsUltrametric =
        true
    ; pAdicBoundaryIsUltrametricIsTrue =
        refl
    ; archimedeanBoundaryIsNotUltrametric =
        true
    ; archimedeanBoundaryIsNotUltrametricIsTrue =
        refl
    ; geometryBookkeepingOnly =
        true
    ; geometryBookkeepingOnlyIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalPromotionIntroduced =
        false
    ; terminalPromotionIntroducedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        adelicSpatialDecompositionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The archimedean component records X0(3^k), X0(4^k), X0(7^k), real hyperbolic geometry, P1(R), and H3WithHyperbolicMetric"
        ∷ "The non-archimedean component records Bruhat-Tits trees T3, T2, T7 and boundary P1(Q3) x P1(Q2) x P1(Q7)"
        ∷ "The p-adic boundary is recorded as ultrametric, while the archimedean boundary is recorded as not ultrametric"
        ∷ "This receipt is geometry bookkeeping only; no Clay/YM or terminal promotion is introduced"
        ∷ []
    }

adelicSpatialDecompositionRecordsUltrametricPAdicBoundary :
  pAdicBoundaryIsUltrametric canonicalAdelicSpatialDecompositionReceipt
  ≡
  true
adelicSpatialDecompositionRecordsUltrametricPAdicBoundary =
  refl

adelicSpatialDecompositionRecordsArchimedeanBoundaryNotUltrametric :
  archimedeanBoundaryIsNotUltrametric canonicalAdelicSpatialDecompositionReceipt
  ≡
  true
adelicSpatialDecompositionRecordsArchimedeanBoundaryNotUltrametric =
  refl

adelicSpatialDecompositionKeepsClayYMFalse :
  clayYangMillsPromoted canonicalAdelicSpatialDecompositionReceipt
  ≡
  false
adelicSpatialDecompositionKeepsClayYMFalse =
  refl

adelicSpatialDecompositionKeepsTerminalFalse :
  terminalPromotionIntroduced canonicalAdelicSpatialDecompositionReceipt
  ≡
  false
adelicSpatialDecompositionKeepsTerminalFalse =
  refl

adelicSpatialDecompositionNoPromotion :
  AdelicSpatialDecompositionPromotion →
  ⊥
adelicSpatialDecompositionNoPromotion =
  adelicSpatialDecompositionPromotionImpossibleHere
