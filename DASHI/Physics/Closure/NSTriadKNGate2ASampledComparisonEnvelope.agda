module DASHI.Physics.Closure.NSTriadKNGate2ASampledComparisonEnvelope where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Properties as NatP using (_≤?_)
open import Relation.Nullary.Decidable.Core using (yes; no)

------------------------------------------------------------------------
-- Gate 2-A sampled quadratic-form comparison envelope.
--
-- This module is the first concrete theorem-facing implementation of the
-- comparison-constant route requested by the 2026-07-02 NS sprint note.
-- It does not claim a proof of the comparison theorem. It records the
-- actual abs/neg two-sided envelopes seen on the dense Schur audit, and
-- the induced obstruction for the naive coarse transport formula.
--
-- The governing theorem shape is:
--
--   c_abs L_good <= Schur(L_abs) <= C_abs L_good
--   c_neg L_bad  <= Schur(L_neg) <= C_neg L_bad
--
-- on 1_C^perp.
--
-- Sampled dense shells:
--   N = 6, 8, 10
--
-- Sampled abs envelopes:
--   N=6:  [1.407, 6.983]
--   N=8:  [1.433, 7.025]
--   N=10: [1.435, 6.879]
--
-- Sampled neg envelopes:
--   N=6:  [1.821, 41.10]
--   N=8:  [1.826, 41.47]
--   N=10: [1.872, 47.80]
--
-- Sampled seam ratios:
--   rho_6  ~= 0.60816
--   rho_8  ~= 0.61283
--   rho_10 ~= 0.61508
--
-- The blunt transport quotient
--
--   rho_transfer <= (C_neg^+ / c_abs^-) * rho_N
--
-- then lands at about 17.77, 17.74, and 20.49, so the coarse route is
-- analytically the wrong target even before any continuum step.

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

four : Nat
four =
  suc three

five : Nat
five =
  suc four

six : Nat
six =
  suc five

seven : Nat
seven =
  suc six

eight : Nat
eight =
  suc seven

nine : Nat
nine =
  suc eight

ten : Nat
ten =
  suc nine

record ScaledRatio : Set where
  constructor mkScaledRatio
  field
    numerator : Nat
    denominator : Nat

open ScaledRatio public

record ComparisonEnvelope : Set where
  constructor mkComparisonEnvelope
  field
    lower : ScaledRatio
    upper : ScaledRatio

open ComparisonEnvelope public

data SampledShell : Set where
  shell6 :
    SampledShell
  shell8 :
    SampledShell
  shell10 :
    SampledShell

canonicalSampledShells : List SampledShell
canonicalSampledShells =
  shell6
  ∷ shell8
  ∷ shell10
  ∷ []

shellValue : SampledShell → Nat
shellValue shell6 = six
shellValue shell8 = eight
shellValue shell10 = ten

shellValue6 : shellValue shell6 ≡ 6
shellValue6 = refl

shellValue8 : shellValue shell8 ≡ 8
shellValue8 = refl

shellValue10 : shellValue shell10 ≡ 10
shellValue10 = refl

-- All sampled decimal constants are recorded as exact scaled integers.
--
-- abs comparison constants use denominator 1000
-- neg comparison constants use denominator 1000 for lower and 100 for upper
-- rho_N uses denominator 100000
-- coarse upper uses denominator 1000
-- directional theta uses denominator 1000000

absEnvelope : SampledShell → ComparisonEnvelope
absEnvelope shell6 =
  mkComparisonEnvelope
    (mkScaledRatio 1407 1000)
    (mkScaledRatio 6983 1000)
absEnvelope shell8 =
  mkComparisonEnvelope
    (mkScaledRatio 1433 1000)
    (mkScaledRatio 7025 1000)
absEnvelope shell10 =
  mkComparisonEnvelope
    (mkScaledRatio 1435 1000)
    (mkScaledRatio 6879 1000)

negEnvelope : SampledShell → ComparisonEnvelope
negEnvelope shell6 =
  mkComparisonEnvelope
    (mkScaledRatio 1821 1000)
    (mkScaledRatio 4110 100)
negEnvelope shell8 =
  mkComparisonEnvelope
    (mkScaledRatio 1826 1000)
    (mkScaledRatio 4147 100)
negEnvelope shell10 =
  mkComparisonEnvelope
    (mkScaledRatio 1872 1000)
    (mkScaledRatio 4780 100)

rhoN : SampledShell → ScaledRatio
rhoN shell6 = mkScaledRatio 60816 100000
rhoN shell8 = mkScaledRatio 61283 100000
rhoN shell10 = mkScaledRatio 61508 100000

coarseUpper : SampledShell → ScaledRatio
coarseUpper shell6 = mkScaledRatio 17766 1000
coarseUpper shell8 = mkScaledRatio 17740 1000
coarseUpper shell10 = mkScaledRatio 20492 1000

directionalTheta : SampledShell → ScaledRatio
directionalTheta shell6 = mkScaledRatio 1681546 10000000
directionalTheta shell8 = mkScaledRatio 1677930 10000000
directionalTheta shell10 = mkScaledRatio 1678154 10000000

quarterTarget : ScaledRatio
quarterTarget =
  mkScaledRatio one four

oneRatio : ScaledRatio
oneRatio =
  mkScaledRatio one one

-- Conservative named comparison constants extracted from the sampled shells.
-- These are background envelope constants only; they do not themselves close
-- Gate 2-A because the induced coarse transport quotient is far too large.

cAbsMinus : ScaledRatio
cAbsMinus =
  mkScaledRatio 1407 1000

cAbsPlus : ScaledRatio
cAbsPlus =
  mkScaledRatio 7025 1000

cNegMinus : ScaledRatio
cNegMinus =
  mkScaledRatio 1821 1000

cNegPlus : ScaledRatio
cNegPlus =
  mkScaledRatio 4780 100

-- Decide whether a scaled ratio is at most 1 by cross-multiplication.
ratioAtMostOne : ScaledRatio → Bool
ratioAtMostOne r with numerator r NatP.≤? denominator r
... | yes _ = true
... | no _ = false

ratioStrictlyAboveOne : ScaledRatio → Bool
ratioStrictlyAboveOne r with ratioAtMostOne r
... | true = false
... | false = true

ratioAtMostQuarter : ScaledRatio → Bool
ratioAtMostQuarter r with ((four * numerator r) NatP.≤? denominator r)
... | yes _ = true
... | no _ = false
  where
  _*_ : Nat → Nat → Nat
  zero * _ = zero
  suc m * n = n + (m * n)

coarseRouteCloses : SampledShell → Bool
coarseRouteCloses s =
  ratioAtMostOne (coarseUpper s)

coarseRouteRejectedBool : SampledShell → Bool
coarseRouteRejectedBool s =
  ratioStrictlyAboveOne (coarseUpper s)

directionalRouteBelowQuarter : SampledShell → Bool
directionalRouteBelowQuarter s =
  ratioAtMostQuarter (directionalTheta s)

shell6CoarseRouteRejected :
  coarseRouteCloses shell6 ≡ false
shell6CoarseRouteRejected = refl

shell8CoarseRouteRejected :
  coarseRouteCloses shell8 ≡ false
shell8CoarseRouteRejected = refl

shell10CoarseRouteRejected :
  coarseRouteCloses shell10 ≡ false
shell10CoarseRouteRejected = refl

shell6DirectionalBelowQuarter :
  directionalRouteBelowQuarter shell6 ≡ true
shell6DirectionalBelowQuarter = refl

shell8DirectionalBelowQuarter :
  directionalRouteBelowQuarter shell8 ≡ true
shell8DirectionalBelowQuarter = refl

shell10DirectionalBelowQuarter :
  directionalRouteBelowQuarter shell10 ≡ true
shell10DirectionalBelowQuarter = refl

record SampledComparisonRow : Set where
  constructor mkSampledComparisonRow
  field
    shell : SampledShell
    absLaw : ComparisonEnvelope
    negLaw : ComparisonEnvelope
    seamRatio : ScaledRatio
    coarseTransportUpper : ScaledRatio
    directionalTransportRatio : ScaledRatio
    coarseRouteRejected : Bool
    directionalBelowQuarter : Bool

open SampledComparisonRow public

sampledRow : SampledShell → SampledComparisonRow
sampledRow s =
  mkSampledComparisonRow
    s
    (absEnvelope s)
    (negEnvelope s)
    (rhoN s)
    (coarseUpper s)
    (directionalTheta s)
    (coarseRouteRejectedBool s)
    (directionalRouteBelowQuarter s)

data Gate2AEnvelopeStatus : Set where
  absComparisonEnvelopeRecorded :
    Gate2AEnvelopeStatus
  negComparisonEnvelopeRecorded :
    Gate2AEnvelopeStatus
  coarseTransportObstructionRecorded :
    Gate2AEnvelopeStatus
  directionalSubcriticalLedgerRecorded :
    Gate2AEnvelopeStatus
  noNSOrClayPromotion :
    Gate2AEnvelopeStatus

canonicalStatuses : List Gate2AEnvelopeStatus
canonicalStatuses =
  absComparisonEnvelopeRecorded
  ∷ negComparisonEnvelopeRecorded
  ∷ coarseTransportObstructionRecorded
  ∷ directionalSubcriticalLedgerRecorded
  ∷ noNSOrClayPromotion
  ∷ []

canonicalLawText : String
canonicalLawText =
  "Sampled Gate 2-A quadratic-form law: c_abs L_good <= Schur(L_abs) <= C_abs L_good and c_neg L_bad <= Schur(L_neg) <= C_neg L_bad on 1_C^perp for the dense sampled shells N=6,8,10."

canonicalObstructionText : String
canonicalObstructionText =
  "The induced coarse transport quotient (C_neg^+ / c_abs^-) rho_N is sampled at about 17.766, 17.740, and 20.492, so the naive worst-case route is analytically obstructed before any downstream PDE step."

canonicalDirectionalText : String
canonicalDirectionalText =
  "Directional seam-extremizer transport remains subcritical on the same shells: theta_6 ~= 0.1681546, theta_8 ~= 0.1677930, theta_10 ~= 0.1678154, all below the conservative quarter target."

canonicalUniformConstantText : String
canonicalUniformConstantText =
  "Conservative sampled background constants: c_abs^- = 1.407, C_abs^+ = 7.025, c_neg^- = 1.821, C_neg^+ = 47.80. These are retained as envelope data, not as the live Gate 2 transport budget."

record NSTriadKNGate2ASampledComparisonEnvelope : Setω where
  constructor mkNSTriadKNGate2ASampledComparisonEnvelope
  field
    statuses : List Gate2AEnvelopeStatus
    statusesAreCanonical :
      statuses ≡ canonicalStatuses

    rows : List SampledComparisonRow
    rowsAreCanonical :
      rows ≡ sampledRow shell6 ∷ sampledRow shell8 ∷ sampledRow shell10 ∷ []

    lawText : String
    lawTextIsCanonical :
      lawText ≡ canonicalLawText

    obstructionText : String
    obstructionTextIsCanonical :
      obstructionText ≡ canonicalObstructionText

    directionalText : String
    directionalTextIsCanonical :
      directionalText ≡ canonicalDirectionalText

    uniformConstantText : String
    uniformConstantTextIsCanonical :
      uniformConstantText ≡ canonicalUniformConstantText

    sampledCAbsMinus : ScaledRatio
    sampledCAbsMinusIsCanonical :
      sampledCAbsMinus ≡ cAbsMinus

    sampledCAbsPlus : ScaledRatio
    sampledCAbsPlusIsCanonical :
      sampledCAbsPlus ≡ cAbsPlus

    sampledCNegMinus : ScaledRatio
    sampledCNegMinusIsCanonical :
      sampledCNegMinus ≡ cNegMinus

    sampledCNegPlus : ScaledRatio
    sampledCNegPlusIsCanonical :
      sampledCNegPlus ≡ cNegPlus

    conservativeSampledEnvelopeConstantsRecorded : Bool
    conservativeSampledEnvelopeConstantsRecordedIsTrue :
      conservativeSampledEnvelopeConstantsRecorded ≡ true

    coarseRouteRejectedOnAllSampledShells : Bool
    coarseRouteRejectedOnAllSampledShellsIsTrue :
      coarseRouteRejectedOnAllSampledShells ≡ true

    directionalRouteBelowQuarterOnAllSampledShells : Bool
    directionalRouteBelowQuarterOnAllSampledShellsIsTrue :
      directionalRouteBelowQuarterOnAllSampledShells ≡ true

    comparisonTheoremProved : Bool
    comparisonTheoremProvedIsFalse :
      comparisonTheoremProved ≡ false

    uniformConstantsProved : Bool
    uniformConstantsProvedIsFalse :
      uniformConstantsProved ≡ false

    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNGate2ASampledComparisonEnvelope public

canonicalNSTriadKNGate2ASampledComparisonEnvelope :
  NSTriadKNGate2ASampledComparisonEnvelope
canonicalNSTriadKNGate2ASampledComparisonEnvelope =
  mkNSTriadKNGate2ASampledComparisonEnvelope
    canonicalStatuses
    refl
    (sampledRow shell6 ∷ sampledRow shell8 ∷ sampledRow shell10 ∷ [])
    refl
    canonicalLawText
    refl
    canonicalObstructionText
    refl
    canonicalDirectionalText
    refl
    canonicalUniformConstantText
    refl
    cAbsMinus
    refl
    cAbsPlus
    refl
    cNegMinus
    refl
    cNegPlus
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
