{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarCanonicalExternalFullSquareRound669Exact where

------------------------------------------------------------------------
-- ROUND669 / R667 EXTERNAL NETWORK ON THE CANONICAL TOTAL ORBIT CARRIER
--
-- R668 gives a useful nonfixed-only residual full-square form, but the repo
-- already owns the stronger R618--R622 orbit-resolved machinery:
--
--   * R618 represents external forcing at fixed OR nonfixed swap orbits;
--   * R621 chooses those cases canonically from literal mode equality;
--   * R616 transports membership from the actual fixed-output fibre.
--
-- Here that total carrier is applied directly to R606's external forcing pair.
-- Only the left/forcing incidence needs the orbit-resolved external vector;
-- the right incidence is the ordinary selected double-mixed cell.  This lets
-- us lift the canonical left representation over the complete ordered square
-- without any legacy R112 witness family or global nonfixedness assumption.
--
-- No estimate, sign, Waleffe-cell identification, or Clay promotion is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.Any as Any
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNDoubleMixedAsSwapPairedPlusMinusRound387Exact as R387
import DASHI.Physics.Closure.NSTriadKNR230SelfExternalNetworkSplitRound605Exact as R605
import DASHI.Physics.Closure.NSTriadKNR567ForcingFullSelfExternalSplitRound606Exact as R606
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNThreeLegResidualMembershipCompilerRound616Exact as R616
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeOrbitResolvedRound619Exact as R619
import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitResolvedSelectionRound621Exact as R621

F : C3.RealField _
F = Rational.rationalRealField

module CanonicalExternalFullSquare
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Split = R606.FixedOutput physicalSystem S output
  module Net = R605.FixedSystem physicalSystem S

  system = Field30.finiteSystem physicalSystem
  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  velocity = Audit.velocityAt system

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Split.fibre

  canonicalSelection :
    (tau : Physical.PhysicalTriadIncidence) →
    tau ∈ fibre →
    R619.ThreeLegOrbitResolvedSelection system tau
  canonicalSelection tau member =
    R621.canonicalThreeLegOrbitResolvedSelection
      system tau
      (R616.canonicalFibreMemberToOwnFibre
        system output tau member)

  canonicalExternalProductRuleCell :
    (tau : Physical.PhysicalTriadIncidence) →
    tau ∈ fibre →
    C3.Complex3 F
  canonicalExternalProductRuleCell tau member =
    let selected = canonicalSelection tau member
    in
    C3.complex3Add
      (Cross.complex3Cross
        (Helical.helicalProjectorPlus E I S
          (Physical.p tau)
          (R619.externalResidualPResolved system tau selected))
        (Helical.helicalProjectorMinus E I S
          (Physical.q tau) (velocity (Physical.q tau))))
      (Cross.complex3Cross
        (Helical.helicalProjectorPlus E I S
          (Physical.p tau) (velocity (Physical.p tau)))
        (Helical.helicalProjectorMinus E I S
          (Physical.q tau)
          (R619.externalResidualQResolved system tau selected)))

  externalProductRuleCellIsCanonical :
    (tau : Physical.PhysicalTriadIncidence) →
    (member : tau ∈ fibre) →
    Net.externalProductRuleCell tau
    ≡ canonicalExternalProductRuleCell tau member
  externalProductRuleCellIsCanonical tau member =
    let selected = canonicalSelection tau member
    in
    cong₂ C3.complex3Add
      (cong
        (λ projected →
          Cross.complex3Cross projected
            (Helical.helicalProjectorMinus E I S
              (Physical.q tau) (velocity (Physical.q tau))))
        (cong
          (Helical.helicalProjectorPlus E I S (Physical.p tau))
          (R619.externalForcingPIsOrbitResolved system tau selected)))
      (cong
        (Cross.complex3Cross
          (Helical.helicalProjectorPlus E I S
            (Physical.p tau) (velocity (Physical.p tau))))
        (cong
          (Helical.helicalProjectorMinus E I S (Physical.q tau))
          (R619.externalForcingQIsOrbitResolved system tau selected)))

  canonicalExternalDoubleForcing :
    (tau : Physical.PhysicalTriadIncidence) →
    tau ∈ fibre →
    C3.Complex3 F
  canonicalExternalDoubleForcing tau member =
    C3.complex3Add
      (R387.doublePlus
        (canonicalExternalProductRuleCell tau member))
      (R387.doublePlus
        (canonicalExternalProductRuleCell
          (Symmetry.swapTriad tau)
          (R224.swapOutputFibreMember member)))

  externalDoubleForcingIsCanonical :
    (tau : Physical.PhysicalTriadIncidence) →
    (member : tau ∈ fibre) →
    Split.externalDoubleForcing tau
    ≡ canonicalExternalDoubleForcing tau member
  externalDoubleForcingIsCanonical tau member =
    cong₂ C3.complex3Add
      (cong R387.doublePlus
        (externalProductRuleCellIsCanonical tau member))
      (cong R387.doublePlus
        (externalProductRuleCellIsCanonical
          (Symmetry.swapTriad tau)
          (R224.swapOutputFibreMember member)))

  canonicalExternalPair :
    (alpha : Physical.PhysicalTriadIncidence) →
    alpha ∈ fibre →
    Physical.PhysicalTriadIncidence → ℚ
  canonicalExternalPair alpha member beta =
    Split.C.T.Swap.pairResolvent alpha beta
      * R179.realHermitianCross
          (canonicalExternalDoubleForcing alpha member)
          (Split.C.Row.doubleCell beta)

  externalPairIsCanonical :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (member : alpha ∈ fibre) →
    Split.externalForcingPair alpha beta
    ≡ canonicalExternalPair alpha member beta
  externalPairIsCanonical alpha beta member =
    cong
      (Split.C.T.Swap.pairResolvent alpha beta *_)
      (cong
        (λ selected →
          R179.realHermitianCross selected (Split.C.Row.doubleCell beta))
        (externalDoubleForcingIsCanonical alpha member))

  canonicalRowSum :
    (alpha : Physical.PhysicalTriadIncidence) →
    alpha ∈ fibre →
    List Physical.PhysicalTriadIncidence → ℚ
  canonicalRowSum alpha member [] = 0
  canonicalRowSum alpha member (beta ∷ rest) =
    canonicalExternalPair alpha member beta
      + canonicalRowSum alpha member rest

  canonicalColumnSum :
    (items : List Physical.PhysicalTriadIncidence) →
    (include : ∀ {tau} → tau ∈ items → tau ∈ fibre) →
    Physical.PhysicalTriadIncidence → ℚ
  canonicalColumnSum [] include beta = 0
  canonicalColumnSum (alpha ∷ rest) include beta =
    canonicalExternalPair alpha (include (Any.here refl)) beta
      + canonicalColumnSum rest
          (λ member → include (Any.there member)) beta

  canonicalFullSquareAux :
    (items : List Physical.PhysicalTriadIncidence) →
    (include : ∀ {tau} → tau ∈ items → tau ∈ fibre) →
    ℚ
  canonicalFullSquareAux [] include = 0
  canonicalFullSquareAux (alpha ∷ rest) include =
    let alphaMember = include (Any.here refl)
        restInclude = λ {tau} member → include (Any.there member)
    in
    canonicalExternalPair alpha alphaMember alpha
      + canonicalRowSum alpha alphaMember rest
      + canonicalColumnSum rest restInclude alpha
      + canonicalFullSquareAux rest restInclude

  rowSumIsCanonical :
    (alpha : Physical.PhysicalTriadIncidence) →
    (member : alpha ∈ fibre) →
    (items : List Physical.PhysicalTriadIncidence) →
    R539.rowSum Split.externalForcingPair alpha items
    ≡ canonicalRowSum alpha member items
  rowSumIsCanonical alpha member [] = refl
  rowSumIsCanonical alpha member (beta ∷ rest) =
    cong₂ _+_
      (externalPairIsCanonical alpha beta member)
      (rowSumIsCanonical alpha member rest)

  columnSumIsCanonical :
    (items : List Physical.PhysicalTriadIncidence) →
    (include : ∀ {tau} → tau ∈ items → tau ∈ fibre) →
    (beta : Physical.PhysicalTriadIncidence) →
    R539.columnSum Split.externalForcingPair items beta
    ≡ canonicalColumnSum items include beta
  columnSumIsCanonical [] include beta = refl
  columnSumIsCanonical (alpha ∷ rest) include beta =
    cong₂ _+_
      (externalPairIsCanonical alpha beta (include (Any.here refl)))
      (columnSumIsCanonical rest
        (λ member → include (Any.there member)) beta)

  fullSquareIsCanonical :
    (items : List Physical.PhysicalTriadIncidence) →
    (include : ∀ {tau} → tau ∈ items → tau ∈ fibre) →
    R543.fullSquareSum Split.externalForcingPair items
    ≡ canonicalFullSquareAux items include
  fullSquareIsCanonical [] include = refl
  fullSquareIsCanonical (alpha ∷ rest) include =
    let alphaMember = include (Any.here refl)
        restInclude = λ {tau} member → include (Any.there member)
    in
    cong₂ _+_
      (cong₂ _+_
        (cong₂ _+_
          (externalPairIsCanonical alpha alpha alphaMember)
          (rowSumIsCanonical alpha alphaMember rest))
        (columnSumIsCanonical rest restInclude alpha))
      (fullSquareIsCanonical rest restInclude)

  canonicalExternalFull : ℚ
  canonicalExternalFull =
    canonicalFullSquareAux fibre (λ member → member)

  externalForcingFullIsCanonicalOrbitResolved :
    Split.externalForcingFull ≡ canonicalExternalFull
  externalForcingFullIsCanonicalOrbitResolved =
    fullSquareIsCanonical fibre (λ member → member)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round669CanonicalOrbitResolvedExternalFullSquareClosed : Bool
round669CanonicalOrbitResolvedExternalFullSquareClosed = true

round669RequiresLegacyR112WitnessFamily : Bool
round669RequiresLegacyR112WitnessFamily = false

round669RequiresGlobalNonfixedness : Bool
round669RequiresGlobalNonfixedness = false

round669PreservesFixedOrbitMultiplicityCorrection : Bool
round669PreservesFixedOrbitMultiplicityCorrection = true

round669ExternalNetworkQuantitativePaymentClosed : Bool
round669ExternalNetworkQuantitativePaymentClosed = false

round669IntroducesEstimate : Bool
round669IntroducesEstimate = false

round669IntroducesNewClayLeaf : Bool
round669IntroducesNewClayLeaf = false

round669C2Closed : Bool
round669C2Closed = false

round669ClayPromotion : Bool
round669ClayPromotion = false

round669CanonicalOrbitResolvedExternalFullSquareClosedIsTrue :
  round669CanonicalOrbitResolvedExternalFullSquareClosed ≡ true
round669CanonicalOrbitResolvedExternalFullSquareClosedIsTrue = refl

round669RequiresLegacyR112WitnessFamilyIsFalse :
  round669RequiresLegacyR112WitnessFamily ≡ false
round669RequiresLegacyR112WitnessFamilyIsFalse = refl

round669RequiresGlobalNonfixednessIsFalse :
  round669RequiresGlobalNonfixedness ≡ false
round669RequiresGlobalNonfixednessIsFalse = refl

round669PreservesFixedOrbitMultiplicityCorrectionIsTrue :
  round669PreservesFixedOrbitMultiplicityCorrection ≡ true
round669PreservesFixedOrbitMultiplicityCorrectionIsTrue = refl

round669ExternalNetworkQuantitativePaymentClosedIsFalse :
  round669ExternalNetworkQuantitativePaymentClosed ≡ false
round669ExternalNetworkQuantitativePaymentClosedIsFalse = refl

round669IntroducesEstimateIsFalse :
  round669IntroducesEstimate ≡ false
round669IntroducesEstimateIsFalse = refl

round669IntroducesNewClayLeafIsFalse :
  round669IntroducesNewClayLeaf ≡ false
round669IntroducesNewClayLeafIsFalse = refl

round669C2ClosedIsFalse :
  round669C2Closed ≡ false
round669C2ClosedIsFalse = refl

round669ClayPromotionIsFalse :
  round669ClayPromotion ≡ false
round669ClayPromotionIsFalse = refl
