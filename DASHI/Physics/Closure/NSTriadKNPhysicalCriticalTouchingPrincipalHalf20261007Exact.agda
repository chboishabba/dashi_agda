module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalHalf20261007Exact where

------------------------------------------------------------------------
-- POSITIVE B4 / SHARP HERMITIAN HALF-MARGIN ON LITERAL CORE-CORE ROWS
--
-- R579 already proves the sharp division-free pair of inequalities
--
--   +2 Re<u,v> <= ||u||^2 + ||v||^2,
--   -2 Re<u,v> <= ||u||^2 + ||v||^2.
--
-- Its convenience absolute-value theorem deliberately weakens this by an
-- extra factor two.  B4's literal companion was defined using that loose
-- envelope.  Recovering the sharp two-sided theorem therefore gives, on EACH
-- SAME Core-Core row and hence on their literal fold,
--
--   P_Core-Core <= (1/2) M_core.
--
-- No PDE estimate, shell hypothesis, spectral gap, or ED remainder enters.
-- The principal half of B4 is therefore closed algebraically.  The remaining
-- strict margin is entirely the Core-noncore defect: it must fit in the other
-- half (possibly plus ED) uniformly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; -_; _*_; _≤_; _<_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRationalHermitianYoungRound579Exact as R579
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Bridge
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact as Rows
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralCompanion20261007Exact as Companion
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalDefectRows20261007Exact as SplitRows

F : C3.RealField _
F = Rational.rationalRealField

oneHalf one : ℚ
oneHalf = Int.+ 1 / 2
one = Int.+ 1 / 1

oneHalfNN : 0ℚ ≤ oneHalf
oneHalfNN = toWitness {a? = 0ℚ ℚP.≤? oneHalf} _

oneHalfStrictlyBelowOne : oneHalf < one
oneHalfStrictlyBelowOne = toWitness {a? = oneHalf ℚP.<? one} _

sharpCoherentWorkMagnitude :
  (u v : C3.Complex3 F) →
  ∣ Work.coherentWork u v ∣
  ≤ L2.complex3NormSquared u + L2.complex3NormSquared v
sharpCoherentWorkMagnitude u v
  with ℚP.∣p∣≡p∨∣p∣≡-p (Work.coherentWork u v)
... | inj₁ absPositive =
  subst
    (_≤ L2.complex3NormSquared u + L2.complex3NormSquared v)
    (sym absPositive)
    (R579.twoRealCrossUpper u v)
... | inj₂ absNegative =
  subst
    (_≤ L2.complex3NormSquared u + L2.complex3NormSquared v)
    (sym absNegative)
    (R579.negTwoRealCrossUpper u v)

sharpWorkDifferenceMagnitude :
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  ∣ Pair.cellWork mixed value alpha - Pair.cellWork mixed value beta ∣
  ≤
  L2.complex3NormSquared mixed
    + L2.complex3NormSquared
        (C3.complex3Subtract (value alpha) (value beta))
sharpWorkDifferenceMagnitude mixed value alpha beta =
  let
    difference = C3.complex3Subtract (value alpha) (value beta)
    bridge = Bridge.cellWorkDifferenceIsVectorDifferenceWork mixed value alpha beta
    sharp = sharpCoherentWorkMagnitude mixed difference
  in
  subst
    (λ selected →
      ∣ selected ∣
      ≤ L2.complex3NormSquared mixed
        + L2.complex3NormSquared difference)
    (sym bridge)
    sharp

rowSignedBelowHalfCompanion :
  (mixed : C3.Complex3 F) →
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (row : Rows.LiteralPairRow) →
  Rows.rowSignedValue rate (Pair.cellWork mixed value) row
  ≤ oneHalf * Companion.rowCompanion mixed rate value row
rowSignedBelowHalfCompanion mixed rate value row =
  let
    alpha = Rows.alpha row
    beta = Rows.beta row
    dr = rate alpha - rate beta
    dw = Pair.cellWork mixed value alpha - Pair.cellWork mixed value beta
    difference = C3.complex3Subtract (value alpha) (value beta)
    mass =
      L2.complex3NormSquared mixed
        + L2.complex3NormSquared difference
    product = dr * dw

    raw : 0ℚ - product ≤ ∣ 0ℚ - product ∣
    raw = ℚP.p≤∣p∣ (0ℚ - product)

    absNeg : ∣ 0ℚ - product ∣ ≡ ∣ product ∣
    absNeg =
      trans
        (cong ∣_∣ (solve (product ∷ []) : 0ℚ - product ≡ - product))
        (ℚP.∣-p∣≡∣p∣ product)

    absProduct : ∣ product ∣ ≡ ∣ dr ∣ * ∣ dw ∣
    absProduct = ℚP.∣p*q∣≡∣p∣*∣q∣ dr dw

    first : 0ℚ - product ≤ ∣ dr ∣ * ∣ dw ∣
    first =
      subst
        (λ upper → 0ℚ - product ≤ upper)
        (trans absNeg absProduct)
        raw

    workSharp : ∣ dw ∣ ≤ mass
    workSharp = sharpWorkDifferenceMagnitude mixed value alpha beta

    scaled : ∣ dr ∣ * ∣ dw ∣ ≤ ∣ dr ∣ * mass
    scaled = ℚP.*-monoˡ-≤-nonNeg ∣ dr ∣ workSharp

    endpoint :
      ∣ dr ∣ * mass
      ≡ oneHalf * Companion.rowCompanion mixed rate value row
    endpoint = solve (∣ dr ∣ ∷ mass ∷ [])
  in
  ℚP.≤-trans first
    (subst (∣ dr ∣ * ∣ dw ∣ ≤_) endpoint scaled)

rowSumBelowHalfCompanion :
  (mixed : C3.Complex3 F) →
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (rows : List Rows.LiteralPairRow) →
  Rows.sumRows rate (Pair.cellWork mixed value) rows
  ≤ oneHalf * Companion.companionSum mixed rate value rows
rowSumBelowHalfCompanion mixed rate value [] =
  subst (0ℚ ≤_) (solve []) ℚP.≤-refl
rowSumBelowHalfCompanion mixed rate value (row ∷ rest) =
  let
    added = ℚP.+-mono-≤
      (rowSignedBelowHalfCompanion mixed rate value row)
      (rowSumBelowHalfCompanion mixed rate value rest)
    endpoint :
      oneHalf * Companion.rowCompanion mixed rate value row
        + oneHalf * Companion.companionSum mixed rate value rest
      ≡ oneHalf * Companion.companionSum mixed rate value (row ∷ rest)
    endpoint = solve
      ( Companion.rowCompanion mixed rate value row
      ∷ Companion.companionSum mixed rate value rest
      ∷ [])
  in
  subst
    (Rows.sumRows rate (Pair.cellWork mixed value) (row ∷ rest) ≤_)
    endpoint
    added

module LivePrincipalHalf
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = Companion.LiveLiteralCompanion physicalSystem S output
  module R = SplitRows.LivePrincipalDefect physicalSystem S output

  principalHalfBound :
    R.principal ≤ oneHalf * Live.coreCompanionMass
  principalHalfBound =
    rowSumBelowHalfCompanion
      (Live.Live.mixed output)
      Live.Rate.inputMass
      Live.Live.value
      R.principalLiteralRows

  record DefectRemainderData : Set where
    constructor defect-remainder-data
    field
      localED : ℚ
      thetaDefect : ℚ
      defectEDCoefficient : ℚ
      thetaDefectNN : 0ℚ ≤ thetaDefect
      halfPlusDefectStrict : oneHalf + thetaDefect < one
      defectBound :
        R.defect
        ≤ thetaDefect * Live.coreCompanionMass
          + defectEDCoefficient * localED

  open DefectRemainderData public

  toLiteralStrictSplit :
    DefectRemainderData → Live.LiteralCompanionStrictSplitData
  toLiteralStrictSplit D = record
    { Live.localED = localED D
    ; Live.thetaPrincipal = oneHalf
    ; Live.thetaDefect = thetaDefect D
    ; Live.principalEDCoefficient = 0ℚ
    ; Live.defectEDCoefficient = defectEDCoefficient D
    ; Live.thetaPrincipalNN = oneHalfNN
    ; Live.thetaDefectNN = thetaDefectNN D
    ; Live.combinedThetaStrictlyBelowOne = halfPlusDefectStrict D
    ; Live.principalStrictBound =
        subst
          (R.principal ≤_)
          (solve (Live.coreCompanionMass ∷ []) :
            oneHalf * Live.coreCompanionMass
            ≡ oneHalf * Live.coreCompanionMass + 0ℚ * localED D)
          principalHalfBound
    ; Live.defectBound = defectBound D
    }

  buildsLiteralB4Certificate :
    (D : DefectRemainderData) →
    Live.G.O.LiteralRowStrictCriticalTouchingCertificate
  buildsLiteralB4Certificate D =
    Live.buildsLiteralB4Certificate (toLiteralStrictSplit D)

b4SharpCoherentWorkYoungClosed : Bool
b4SharpCoherentWorkYoungClosed = true

b4PrincipalHalfCompanionBoundClosed : Bool
b4PrincipalHalfCompanionBoundClosed = true

b4PrincipalNeedsEDRemainder : Bool
b4PrincipalNeedsEDRemainder = false

b4RemainingStrictMarginIsDefectBelowHalf : Bool
b4RemainingStrictMarginIsDefectBelowHalf = true

b4DefectRemainderClosed : Bool
b4DefectRemainderClosed = false

clayPromotion : Bool
clayPromotion = false

b4SharpCoherentWorkYoungClosedIsTrue :
  b4SharpCoherentWorkYoungClosed ≡ true
b4SharpCoherentWorkYoungClosedIsTrue = refl

b4PrincipalHalfCompanionBoundClosedIsTrue :
  b4PrincipalHalfCompanionBoundClosed ≡ true
b4PrincipalHalfCompanionBoundClosedIsTrue = refl

b4PrincipalNeedsEDRemainderIsFalse :
  b4PrincipalNeedsEDRemainder ≡ false
b4PrincipalNeedsEDRemainderIsFalse = refl

b4RemainingStrictMarginIsDefectBelowHalfIsTrue :
  b4RemainingStrictMarginIsDefectBelowHalf ≡ true
b4RemainingStrictMarginIsDefectBelowHalfIsTrue = refl
