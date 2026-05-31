module DASHI.Physics.Closure.YM4DConformalInvarianceReceipt where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Four-dimensional Yang-Mills conformal-invariance receipt.
--
-- This receipt records the classical four-dimensional Yang-Mills scaling
-- bookkeeping under a Weyl rescaling g_{mu nu} -> Omega^2 g_{mu nu}.  The
-- gauge potential A_mu and curvature F_mu nu are held invariant, the raised
-- contraction |F|^2 scales as Omega^-4, and the four-dimensional volume form
-- scales as Omega^4, so the action S = 1/(2g^2) integral Tr |F|^2 d^4x is
-- invariant.
--
-- It also records the Poincare model of H4:
-- ds^2 = (|dx|^2 + dt^2)/t^2 = Omega^2 flat metric, Omega = 1/t.  Constant-t
-- spatial slices are flat R3 slices, not H3; consequently H3 x R+ is not H4.

data YM4DConformalInvarianceStatus : Set where
  theorem :
    YM4DConformalInvarianceStatus

data YM4DConformalInvarianceFact : Set where
  fourDimensionalYangMillsAction :
    YM4DConformalInvarianceFact

  weylMetricRescaling :
    YM4DConformalInvarianceFact

  gaugePotentialInvariant :
    YM4DConformalInvarianceFact

  curvatureTwoFormInvariant :
    YM4DConformalInvarianceFact

  curvatureNormScalesOmegaMinusFour :
    YM4DConformalInvarianceFact

  fourDimensionalVolumeScalesOmegaFour :
    YM4DConformalInvarianceFact

  yangMillsActionConformallyInvariant :
    YM4DConformalInvarianceFact

  poincareH4MetricConformalToFlat :
    YM4DConformalInvarianceFact

  poincareH4ConformalFactorOneOverT :
    YM4DConformalInvarianceFact

  constantTSlicesFlatR3 :
    YM4DConformalInvarianceFact

  constantTSlicesNotH3 :
    YM4DConformalInvarianceFact

  H3timesR+IsNotH4Fact :
    YM4DConformalInvarianceFact

canonicalYM4DConformalInvarianceFacts :
  List YM4DConformalInvarianceFact
canonicalYM4DConformalInvarianceFacts =
  fourDimensionalYangMillsAction
  ∷ weylMetricRescaling
  ∷ gaugePotentialInvariant
  ∷ curvatureTwoFormInvariant
  ∷ curvatureNormScalesOmegaMinusFour
  ∷ fourDimensionalVolumeScalesOmegaFour
  ∷ yangMillsActionConformallyInvariant
  ∷ poincareH4MetricConformalToFlat
  ∷ poincareH4ConformalFactorOneOverT
  ∷ constantTSlicesFlatR3
  ∷ constantTSlicesNotH3
  ∷ H3timesR+IsNotH4Fact
  ∷ []

ym4DActionStatement :
  String
ym4DActionStatement =
  "4D Yang-Mills action S = 1/(2g^2) integral Tr |F|^2 d^4x."

ym4DConformalInvarianceStatement :
  String
ym4DConformalInvarianceStatement =
  "Under g_{mu nu} -> Omega^2 g_{mu nu}, A_mu and F_mu nu are invariant, |F|^2 scales as Omega^-4, and d^4x volume scales as Omega^4; therefore the 4D Yang-Mills action is conformally invariant."

poincareH4Statement :
  String
poincareH4Statement =
  "Poincare H4 metric ds^2 = (|dx|^2 + dt^2)/t^2 = Omega^2 flat metric with Omega = 1/t."

poincareH4SliceStatement :
  String
poincareH4SliceStatement =
  "Constant-t spatial slices in the Poincare H4 model are flat R3 slices, not H3; H3 x R+ is not H4."

record YM4DConformalInvarianceReceipt : Set where
  field
    status :
      YM4DConformalInvarianceStatus

    4DYMIsConformallyInvariant :
      YM4DConformalInvarianceStatus

    4DYMIsConformallyInvariantIsTheorem :
      4DYMIsConformallyInvariant ≡ theorem

    facts :
      List YM4DConformalInvarianceFact

    factsAreCanonical :
      facts ≡ canonicalYM4DConformalInvarianceFacts

    actionFormula :
      String

    actionFormulaIsCanonical :
      actionFormula ≡ "S = 1/(2g^2) integral Tr |F|^2 d^4x"

    weylRescaling :
      String

    weylRescalingIsCanonical :
      weylRescaling ≡ "g_{mu nu} -> Omega^2 g_{mu nu}"

    gaugePotentialScaling :
      String

    gaugePotentialScalingIsInvariant :
      gaugePotentialScaling ≡ "A_mu invariant"

    curvatureScaling :
      String

    curvatureScalingIsInvariant :
      curvatureScaling ≡ "F_mu nu invariant"

    curvatureNormScaling :
      String

    curvatureNormScalingIsOmegaMinusFour :
      curvatureNormScaling ≡ "|F|^2 scales Omega^-4"

    volumeScaling :
      String

    volumeScalingIsOmegaFour :
      volumeScaling ≡ "volume scales Omega^4"

    poincareH4Metric :
      String

    poincareH4MetricIsCanonical :
      poincareH4Metric ≡ "ds^2 = (|dx|^2 + dt^2)/t^2"

    poincareH4ConformalFactor :
      String

    poincareH4ConformalFactorIsOneOverT :
      poincareH4ConformalFactor ≡ "Omega = 1/t"

    poincareH4HasFlatR3Slices :
      Bool

    poincareH4HasFlatR3SlicesIsTrue :
      poincareH4HasFlatR3Slices ≡ true

    H3timesR+IsNotH4 :
      Bool

    H3timesR+IsNotH4IsTrue :
      H3timesR+IsNotH4 ≡ true

    actionStatement :
      String

    actionStatementIsCanonical :
      actionStatement ≡ ym4DActionStatement

    conformalInvarianceStatement :
      String

    conformalInvarianceStatementIsCanonical :
      conformalInvarianceStatement ≡ ym4DConformalInvarianceStatement

    poincareModelStatement :
      String

    poincareModelStatementIsCanonical :
      poincareModelStatement ≡ poincareH4Statement

    sliceStatement :
      String

    sliceStatementIsCanonical :
      sliceStatement ≡ poincareH4SliceStatement

open YM4DConformalInvarianceReceipt public

canonicalYM4DConformalInvarianceReceipt :
  YM4DConformalInvarianceReceipt
canonicalYM4DConformalInvarianceReceipt =
  record
    { status =
        theorem
    ; 4DYMIsConformallyInvariant =
        theorem
    ; 4DYMIsConformallyInvariantIsTheorem =
        refl
    ; facts =
        canonicalYM4DConformalInvarianceFacts
    ; factsAreCanonical =
        refl
    ; actionFormula =
        "S = 1/(2g^2) integral Tr |F|^2 d^4x"
    ; actionFormulaIsCanonical =
        refl
    ; weylRescaling =
        "g_{mu nu} -> Omega^2 g_{mu nu}"
    ; weylRescalingIsCanonical =
        refl
    ; gaugePotentialScaling =
        "A_mu invariant"
    ; gaugePotentialScalingIsInvariant =
        refl
    ; curvatureScaling =
        "F_mu nu invariant"
    ; curvatureScalingIsInvariant =
        refl
    ; curvatureNormScaling =
        "|F|^2 scales Omega^-4"
    ; curvatureNormScalingIsOmegaMinusFour =
        refl
    ; volumeScaling =
        "volume scales Omega^4"
    ; volumeScalingIsOmegaFour =
        refl
    ; poincareH4Metric =
        "ds^2 = (|dx|^2 + dt^2)/t^2"
    ; poincareH4MetricIsCanonical =
        refl
    ; poincareH4ConformalFactor =
        "Omega = 1/t"
    ; poincareH4ConformalFactorIsOneOverT =
        refl
    ; poincareH4HasFlatR3Slices =
        true
    ; poincareH4HasFlatR3SlicesIsTrue =
        refl
    ; H3timesR+IsNotH4 =
        true
    ; H3timesR+IsNotH4IsTrue =
        refl
    ; actionStatement =
        ym4DActionStatement
    ; actionStatementIsCanonical =
        refl
    ; conformalInvarianceStatement =
        ym4DConformalInvarianceStatement
    ; conformalInvarianceStatementIsCanonical =
        refl
    ; poincareModelStatement =
        poincareH4Statement
    ; poincareModelStatementIsCanonical =
        refl
    ; sliceStatement =
        poincareH4SliceStatement
    ; sliceStatementIsCanonical =
        refl
    }

4DYMIsConformallyInvariantFlag :
  4DYMIsConformallyInvariant canonicalYM4DConformalInvarianceReceipt
  ≡
  theorem
4DYMIsConformallyInvariantFlag =
  refl

poincareH4HasFlatR3SlicesFlag :
  poincareH4HasFlatR3Slices canonicalYM4DConformalInvarianceReceipt
  ≡
  true
poincareH4HasFlatR3SlicesFlag =
  refl

H3timesR+IsNotH4Flag :
  H3timesR+IsNotH4 canonicalYM4DConformalInvarianceReceipt
  ≡
  true
H3timesR+IsNotH4Flag =
  refl
