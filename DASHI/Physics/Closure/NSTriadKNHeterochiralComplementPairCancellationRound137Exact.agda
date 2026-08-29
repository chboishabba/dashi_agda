module DASHI.Physics.Closure.NSTriadKNHeterochiralComplementPairCancellationRound137Exact where

------------------------------------------------------------------------
-- ROUND137 / COMPLEMENTARY HETEROCHIRAL PAIRING BEFORE ABSOLUTE VALUES
--
-- Source: Fabian Waleffe, "The nature of triad interactions in homogeneous
-- turbulence", Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--
-- Round135 exhausts the eight helicity sign classes.  The two homochiral
-- classes vanish.  The six remaining classes occur in three complementary
-- pairs obtained by flipping every helicity sign while retaining which LEG is
-- the minority sign.
--
-- For fixed radii and class amplitudes, the two members of each pair have
-- opposite coefficients.  Therefore their SIGNED sum depends only on the
-- difference of the two complementary amplitudes:
--
--   k-minority pair
--     = 2 r_k (r_q-r_p) (A_-++ - A_+--),
--
-- and cyclically for p and q.
--
-- This is important structurally: a cellwise absolute-value estimate throws
-- away exactly this cancellation.  The live nonlinear object is therefore a
-- CHIRAL-IMBALANCE amplitude, not the sum of the two absolute amplitudes.
--
-- No claim is made here that the complementary amplitudes are equal.  The next
-- producer must identify their relation on the actual helical decomposition of
-- one physical velocity field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNPhysicalHelicitySignExhaustionRound135Exact as R135

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

  two : ∀ {r} (F : C3.RealField r) → C3.Carrier F
  two F = C3.add F (C3.one F) (C3.one F)

  pairCoefficient :
    ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
  pairCoefficient {F = F} minority left right =
    C3.multiply F
      (C3.multiply F (two F) minority)
      (sub left right)

------------------------------------------------------------------------
-- Each complementary pair collapses to coefficient * amplitude difference.
------------------------------------------------------------------------

kMinorityComplementPair :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq aMinus aPlus : C3.Carrier F) →
  C3.add F
    (R135.minorityNormalForm
      R135.minus R135.plus R135.plus rk rp rq aMinus)
    (R135.minorityNormalForm
      R135.plus R135.minus R135.minus rk rp rq aPlus)
  ≡ C3.multiply F
      (pairCoefficient rk rq rp)
      (sub aMinus aPlus)
kMinorityComplementPair {F = F} rk rp rq aMinus aPlus =
  P.R.solve 5
    (λ rk rp rq am ap →
      (((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rk)
          P.R.⊗ (rq P.R.⊕ (P.R.⊝ rp))) P.R.⊗ am)
        P.R.⊕
        (P.R.⊝
          ((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rk)
            P.R.⊗ (rq P.R.⊕ (P.R.⊝ rp))) P.R.⊗ ap)))
      P.R.⊜
      ((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rk)
          P.R.⊗ (rq P.R.⊕ (P.R.⊝ rp)))
        P.R.⊗ (am P.R.⊕ (P.R.⊝ ap))))
    refl rk rp rq aMinus aPlus
  where module P = Field.Polynomial F

pMinorityComplementPair :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq aMinus aPlus : C3.Carrier F) →
  C3.add F
    (R135.minorityNormalForm
      R135.plus R135.minus R135.plus rk rp rq aMinus)
    (R135.minorityNormalForm
      R135.minus R135.plus R135.minus rk rp rq aPlus)
  ≡ C3.multiply F
      (pairCoefficient rp rk rq)
      (sub aMinus aPlus)
pMinorityComplementPair {F = F} rk rp rq aMinus aPlus =
  P.R.solve 5
    (λ rk rp rq am ap →
      (((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rp)
          P.R.⊗ (rk P.R.⊕ (P.R.⊝ rq))) P.R.⊗ am)
        P.R.⊕
        (P.R.⊝
          ((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rp)
            P.R.⊗ (rk P.R.⊕ (P.R.⊝ rq))) P.R.⊗ ap)))
      P.R.⊜
      ((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rp)
          P.R.⊗ (rk P.R.⊕ (P.R.⊝ rq)))
        P.R.⊗ (am P.R.⊕ (P.R.⊝ ap))))
    refl rk rp rq aMinus aPlus
  where module P = Field.Polynomial F

qMinorityComplementPair :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq aMinus aPlus : C3.Carrier F) →
  C3.add F
    (R135.minorityNormalForm
      R135.plus R135.plus R135.minus rk rp rq aMinus)
    (R135.minorityNormalForm
      R135.minus R135.minus R135.plus rk rp rq aPlus)
  ≡ C3.multiply F
      (pairCoefficient rq rp rk)
      (sub aMinus aPlus)
qMinorityComplementPair {F = F} rk rp rq aMinus aPlus =
  P.R.solve 5
    (λ rk rp rq am ap →
      (((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rq)
          P.R.⊗ (rp P.R.⊕ (P.R.⊝ rk))) P.R.⊗ am)
        P.R.⊕
        (P.R.⊝
          ((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rq)
            P.R.⊗ (rp P.R.⊕ (P.R.⊝ rk))) P.R.⊗ ap)))
      P.R.⊜
      ((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rq)
          P.R.⊗ (rp P.R.⊕ (P.R.⊝ rk)))
        P.R.⊗ (am P.R.⊕ (P.R.⊝ ap))))
    refl rk rp rq aMinus aPlus
  where module P = Field.Polynomial F

------------------------------------------------------------------------
-- The full six-class signed heterochiral production is a sum of THREE
-- chiral-imbalance amplitudes.
------------------------------------------------------------------------

sixClassProduction :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F → C3.Carrier F
sixClassProduction {F = F}
    rk rp rq akMinus akPlus apMinus apPlus aqMinus aqPlus =
  C3.add F
    (C3.add F
      (R135.minorityNormalForm R135.minus R135.plus R135.plus
        rk rp rq akMinus)
      (R135.minorityNormalForm R135.plus R135.minus R135.minus
        rk rp rq akPlus))
    (C3.add F
      (C3.add F
        (R135.minorityNormalForm R135.plus R135.minus R135.plus
          rk rp rq apMinus)
        (R135.minorityNormalForm R135.minus R135.plus R135.minus
          rk rp rq apPlus))
      (C3.add F
        (R135.minorityNormalForm R135.plus R135.plus R135.minus
          rk rp rq aqMinus)
        (R135.minorityNormalForm R135.minus R135.minus R135.plus
          rk rp rq aqPlus)))

chiralImbalanceProduction :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F → C3.Carrier F
chiralImbalanceProduction {F = F}
    rk rp rq akMinus akPlus apMinus apPlus aqMinus aqPlus =
  C3.add F
    (C3.multiply F (pairCoefficient rk rq rp) (sub akMinus akPlus))
    (C3.add F
      (C3.multiply F (pairCoefficient rp rk rq) (sub apMinus apPlus))
      (C3.multiply F (pairCoefficient rq rp rk) (sub aqMinus aqPlus)))

sixClassProductionIsChiralImbalance :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq akMinus akPlus apMinus apPlus aqMinus aqPlus : C3.Carrier F) →
  sixClassProduction rk rp rq
    akMinus akPlus apMinus apPlus aqMinus aqPlus
  ≡ chiralImbalanceProduction rk rp rq
    akMinus akPlus apMinus apPlus aqMinus aqPlus
sixClassProductionIsChiralImbalance {F = F}
    rk rp rq akMinus akPlus apMinus apPlus aqMinus aqPlus =
  P.R.solve 9
    (λ rk rp rq akm akp apm app aqm aqp →
      (((((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rk)
              P.R.⊗ (rq P.R.⊕ (P.R.⊝ rp))) P.R.⊗ akm)
          P.R.⊕
          (P.R.⊝ ((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rk)
              P.R.⊗ (rq P.R.⊕ (P.R.⊝ rp))) P.R.⊗ akp)))
        P.R.⊕
        (((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rp)
              P.R.⊗ (rk P.R.⊕ (P.R.⊝ rq))) P.R.⊗ apm)
          P.R.⊕
          (P.R.⊝ ((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rp)
              P.R.⊗ (rk P.R.⊕ (P.R.⊝ rq))) P.R.⊗ app))))
        P.R.⊕
        (((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rq)
              P.R.⊗ (rp P.R.⊕ (P.R.⊝ rk))) P.R.⊗ aqm)
          P.R.⊕
          (P.R.⊝ ((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rq)
              P.R.⊗ (rp P.R.⊕ (P.R.⊝ rk))) P.R.⊗ aqp))))
      P.R.⊜
      (((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rk)
          P.R.⊗ (rq P.R.⊕ (P.R.⊝ rp))) P.R.⊗ (akm P.R.⊕ (P.R.⊝ akp)))
       P.R.⊕
       (((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rp)
          P.R.⊗ (rk P.R.⊕ (P.R.⊝ rq))) P.R.⊗ (apm P.R.⊕ (P.R.⊝ app)))
        P.R.⊕
        ((((P.R.Κ (C3.one F) P.R.⊕ P.R.Κ (C3.one F)) P.R.⊗ rq)
          P.R.⊗ (rp P.R.⊕ (P.R.⊝ rk))) P.R.⊗ (aqm P.R.⊕ (P.R.⊝ aqp))))))
    refl rk rp rq akMinus akPlus apMinus apPlus aqMinus aqPlus
  where module P = Field.Polynomial F

round137ComplementaryHelicityClassesPairedBeforeAbs : Bool
round137ComplementaryHelicityClassesPairedBeforeAbs = true

round137SixMixedClassesReduceToThreeChiralImbalances : Bool
round137SixMixedClassesReduceToThreeChiralImbalances = true

round137ComplementaryAmplitudeEqualityClaimed : Bool
round137ComplementaryAmplitudeEqualityClaimed = false

round137PhysicalChiralImbalancePaymentClosed : Bool
round137PhysicalChiralImbalancePaymentClosed = false

round137PackageAClosed : Bool
round137PackageAClosed = false

round137SixMixedClassesReduceToThreeChiralImbalancesIsTrue :
  round137SixMixedClassesReduceToThreeChiralImbalances ≡ true
round137SixMixedClassesReduceToThreeChiralImbalancesIsTrue = refl

round137PackageAClosedIsFalse : round137PackageAClosed ≡ false
round137PackageAClosedIsFalse = refl
