module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact where

------------------------------------------------------------------------
-- S2b2d1b2 / A2 EXACT PHYSICAL VISCOUS RATE DIFFERENCE
--
-- The covariance carrier uses
--
--   cellRate rho tau = rho(p_tau) + rho(q_tau).
--
-- The live physical Galerkin owner already defines, on the SAME rational
-- carrier,
--
--   physicalDecayRate(mode) = nu * normSquared(mode).
--
-- This module performs only that same-object specialization and subtraction.
-- No sign, lower bound, Pluecker estimate, absolute value, or payment is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as PhysicalField
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair

F : C3.RealField _
F = Rational.rationalRealField

physicalModalRate :
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Z3.FourierMode → ℚ
physicalModalRate = R94.physicalDecayRate

physicalCellRate :
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Physical.PhysicalTriadIncidence → ℚ
physicalCellRate system = Pair.cellRate (physicalModalRate system)

literalViscousCellRate :
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Physical.PhysicalTriadIncidence → ℚ
literalViscousCellRate system tau =
  C3.multiply F
    (PhysicalField.viscosity system)
    (C3.normSquared
      (Audit.inverseSquare (PhysicalField.finiteSystem system))
      (Physical.p tau))
  +
  C3.multiply F
    (PhysicalField.viscosity system)
    (C3.normSquared
      (Audit.inverseSquare (PhysicalField.finiteSystem system))
      (Physical.q tau))

physicalCellRateIsLiteralViscousRate :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (tau : Physical.PhysicalTriadIncidence) →
  physicalCellRate system tau ≡ literalViscousCellRate system tau
physicalCellRateIsLiteralViscousRate system tau = refl

physicalRateDifference :
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
physicalRateDifference system alpha beta =
  literalViscousCellRate system alpha - literalViscousCellRate system beta

physicalCellRateDifference :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Pair.cellRate (R94.physicalDecayRate system) alpha
    - Pair.cellRate (R94.physicalDecayRate system) beta
  ≡ physicalRateDifference system alpha beta
physicalCellRateDifference system alpha beta =
  cong₂ _-_
    (physicalCellRateIsLiteralViscousRate system alpha)
    (physicalCellRateIsLiteralViscousRate system beta)


------------------------------------------------------------------------
-- Fixed-output rate geometry: exact division-free factorization.
------------------------------------------------------------------------

two : ℚ
two = 1ℚ + 1ℚ

differenceMode :
  Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
differenceMode q p = Z3.addMode q (Z3.negateMode p)

liveParallelogramForSumDifference :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (p q : Z3.FourierMode) →
  C3.normSquared I (differenceMode q p)
    + C3.normSquared I (Z3.addMode p q)
  ≡ two * (C3.normSquared I p + C3.normSquared I q)
liveParallelogramForSumDifference E I
    (Z3.mode px py pz) (Z3.mode qx qy qz)
  rewrite C3.normSquaredMeaning I
      (differenceMode (Z3.mode qx qy qz) (Z3.mode px py pz))
        | C3.normSquaredMeaning I
            (Z3.addMode (Z3.mode px py pz) (Z3.mode qx qy qz))
        | C3.normSquaredMeaning I (Z3.mode px py pz)
        | C3.normSquaredMeaning I (Z3.mode qx qy qz)
        | C3.embedAdd E qx (- px)
        | C3.embedAdd E qy (- py)
        | C3.embedAdd E qz (- pz)
        | C3.embedNegate E px
        | C3.embedNegate E py
        | C3.embedNegate E pz
        | C3.embedAdd E px qx
        | C3.embedAdd E py qy
        | C3.embedAdd E pz qz =
  solve
    ( C3.embedInteger E px
    ∷ C3.embedInteger E py
    ∷ C3.embedInteger E pz
    ∷ C3.embedInteger E qx
    ∷ C3.embedInteger E qy
    ∷ C3.embedInteger E qz
    ∷ [])

liveResonantParallelogram :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (tau : Physical.PhysicalTriadIncidence) →
  let
    I = PhysicalField.physicalInverseSquare system
    p = Physical.p tau
    q = Physical.q tau
    k = Physical.k tau
  in
  C3.normSquared I (differenceMode q p)
    + C3.normSquared I k
  ≡ two * (C3.normSquared I p + C3.normSquared I q)
liveResonantParallelogram system tau =
  trans
    (cong
      (C3.normSquared (PhysicalField.physicalInverseSquare system)
        (differenceMode (Physical.q tau) (Physical.p tau)) +_)
      (sym (cong
        (C3.normSquared (PhysicalField.physicalInverseSquare system))
        (Physical.resonance tau))))
    (liveParallelogramForSumDifference
      (PhysicalField.physicalEmbedding system)
      (PhysicalField.physicalInverseSquare system)
      (Physical.p tau)
      (Physical.q tau))

physicalRateDifferenceSameOutputFactorization :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  let
    I = PhysicalField.physicalInverseSquare system
    nu = PhysicalField.viscosity system
  in
  two * physicalRateDifference system alpha beta
  ≡ nu *
      ( C3.normSquared I
          (differenceMode (Physical.q alpha) (Physical.p alpha))
      - C3.normSquared I
          (differenceMode (Physical.q beta) (Physical.p beta)))
physicalRateDifferenceSameOutputFactorization system alpha beta sameOutput =
  let
    I = PhysicalField.physicalInverseSquare system
    nu = PhysicalField.viscosity system

    ap = C3.normSquared I (Physical.p alpha)
    aq = C3.normSquared I (Physical.q alpha)
    ak = C3.normSquared I (Physical.k alpha)
    ad = C3.normSquared I
      (differenceMode (Physical.q alpha) (Physical.p alpha))

    bp = C3.normSquared I (Physical.p beta)
    bq = C3.normSquared I (Physical.q beta)
    bk = C3.normSquared I (Physical.k beta)
    bd = C3.normSquared I
      (differenceMode (Physical.q beta) (Physical.p beta))

    paraA : ad + ak ≡ two * (ap + aq)
    paraA = liveResonantParallelogram system alpha

    paraB : bd + bk ≡ two * (bp + bq)
    paraB = liveResonantParallelogram system beta

    sameOutputNorm : ak ≡ bk
    sameOutputNorm = cong (C3.normSquared I) sameOutput

    doubledRate :
      two * physicalRateDifference system alpha beta
      ≡ nu * (two * (ap + aq) - two * (bp + bq))
    doubledRate = solve (nu ∷ ap ∷ aq ∷ bp ∷ bq ∷ [])

    geometricDifference :
      two * (ap + aq) - two * (bp + bq)
      ≡ ad - bd
    geometricDifference
      rewrite sym paraA | sym paraB | sameOutputNorm =
      solve (ad ∷ bd ∷ bk ∷ [])
  in
  trans doubledRate (cong (nu *_) geometricDifference)



------------------------------------------------------------------------
-- Same-output fibre certificate and pair-sum rate factorization.
------------------------------------------------------------------------

data AllSameOutput
    (output : Z3.FourierMode) :
    List Physical.PhysicalTriadIncidence → Set where
  allSameOutputNil : AllSameOutput output []
  allSameOutputCons :
    ∀ {head tail} →
    Physical.k head ≡ output →
    AllSameOutput output tail →
    AllSameOutput output (head ∷ tail)

filterOutputAllSame :
  (output : Z3.FourierMode) →
  (items : List Physical.PhysicalTriadIncidence) →
  AllSameOutput output (Output.filterOutput output items)
filterOutputAllSame output [] = allSameOutputNil
filterOutputAllSame output (head ∷ tail)
  with Output.modeEqual (Physical.k head) output in eq
... | true =
  allSameOutputCons
    (Output.modeEqualSound eq)
    (filterOutputAllSame output tail)
... | false = filterOutputAllSame output tail

physicalOutputFiberAllSame :
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  AllSameOutput output (Output.physicalOutputFiber cutoff output)
physicalOutputFiberAllSame cutoff output =
  filterOutputAllSame output (Physical.physicalTriadEnumeration cutoff)

separationNormSquared :
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Physical.PhysicalTriadIncidence → ℚ
separationNormSquared system tau =
  C3.normSquared
    (PhysicalField.physicalInverseSquare system)
    (differenceMode (Physical.q tau) (Physical.p tau))

sameOutputRateDifferenceFactorization :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (output : Z3.FourierMode) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ output →
  Physical.k beta ≡ output →
  two *
    ( physicalCellRate system alpha
    - physicalCellRate system beta )
  ≡ PhysicalField.viscosity system *
    ( separationNormSquared system alpha
    - separationNormSquared system beta )
sameOutputRateDifferenceFactorization
    system output alpha beta alphaOutput betaOutput =
  trans
    (cong (two *_) (physicalCellRateDifference system alpha beta))
    (physicalRateDifferenceSameOutputFactorization
      system alpha beta (trans alphaOutput (sym betaOutput)))

pairAgainstHeadGeometric :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → ℚ
pairAgainstHeadGeometric system work head [] = 0
pairAgainstHeadGeometric system work head (x ∷ xs) =
  ( separationNormSquared system head
  - separationNormSquared system x )
  * (work head - work x)
  + pairAgainstHeadGeometric system work head xs

pairDifferenceGeometric :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
pairDifferenceGeometric system work [] = 0
pairDifferenceGeometric system work (x ∷ xs) =
  pairAgainstHeadGeometric system work x xs
  + pairDifferenceGeometric system work xs

pairAgainstHeadRateToGeometry :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (output : Z3.FourierMode) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  (head : Physical.PhysicalTriadIncidence) →
  (xs : List Physical.PhysicalTriadIncidence) →
  Physical.k head ≡ output →
  AllSameOutput output xs →
  two *
    Pair.pairAgainstHead
      (physicalCellRate system) work head xs
  ≡ PhysicalField.viscosity system
      * pairAgainstHeadGeometric system work head xs
pairAgainstHeadRateToGeometry system output work head []
    headOutput allSameOutputNil =
  solve (PhysicalField.viscosity system ∷ [])
pairAgainstHeadRateToGeometry system output work head (x ∷ xs)
    headOutput (allSameOutputCons xOutput tailOutput) =
  let
    rateFactor :
      two *
        ( physicalCellRate system head
        - physicalCellRate system x )
      ≡ PhysicalField.viscosity system *
        ( separationNormSquared system head
        - separationNormSquared system x )
    rateFactor =
      sameOutputRateDifferenceFactorization
        system output head x headOutput xOutput

    tailFactor :
      two *
        Pair.pairAgainstHead
          (physicalCellRate system) work head xs
      ≡ PhysicalField.viscosity system
          * pairAgainstHeadGeometric system work head xs
    tailFactor =
      pairAgainstHeadRateToGeometry
        system output work head xs headOutput tailOutput
  in
  let
    dr =
      physicalCellRate system head - physicalCellRate system x
    dg =
      separationNormSquared system head - separationNormSquared system x
    dw = work head - work x
    tailR =
      Pair.pairAgainstHead
        (physicalCellRate system) work head xs
    tailG = pairAgainstHeadGeometric system work head xs
    nu = PhysicalField.viscosity system
  in
  trans
    (solve (dr ∷ dw ∷ tailR ∷ []))
    (trans
      (cong₂ _+_
        (cong (_* dw) rateFactor)
        tailFactor)
      (solve (nu ∷ dg ∷ dw ∷ tailG ∷ [])))

pairDifferenceRateToGeometry :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (output : Z3.FourierMode) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  AllSameOutput output items →
  two *
    Pair.pairDifferenceWorkSum
      (physicalCellRate system) work items
  ≡ PhysicalField.viscosity system
      * pairDifferenceGeometric system work items
pairDifferenceRateToGeometry system output work []
    allSameOutputNil =
  solve (PhysicalField.viscosity system ∷ [])
pairDifferenceRateToGeometry system output work (x ∷ xs)
    (allSameOutputCons xOutput tailOutput) =
  let
    headFactor =
      pairAgainstHeadRateToGeometry
        system output work x xs xOutput tailOutput
    tailFactor =
      pairDifferenceRateToGeometry
        system output work xs tailOutput

    headR =
      Pair.pairAgainstHead
        (physicalCellRate system) work x xs
    tailR =
      Pair.pairDifferenceWorkSum
        (physicalCellRate system) work xs
    headG = pairAgainstHeadGeometric system work x xs
    tailG = pairDifferenceGeometric system work xs
    nu = PhysicalField.viscosity system
  in
  trans
    (solve (headR ∷ tailR ∷ []))
    (trans
      (cong₂ _+_ headFactor tailFactor)
      (solve (nu ∷ headG ∷ tailG ∷ [])))

physicalOutputFiberPairDifferenceRateToGeometry :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (output : Z3.FourierMode) →
  (work : Physical.PhysicalTriadIncidence → ℚ) →
  two *
    Pair.pairDifferenceWorkSum
      (physicalCellRate system) work
      (Output.physicalOutputFiber
        (Audit.cutoff (PhysicalField.finiteSystem system)) output)
  ≡ PhysicalField.viscosity system *
      pairDifferenceGeometric system work
        (Output.physicalOutputFiber
          (Audit.cutoff (PhysicalField.finiteSystem system)) output)
physicalOutputFiberPairDifferenceRateToGeometry system output work =
  pairDifferenceRateToGeometry
    system output work
    (Output.physicalOutputFiber
      (Audit.cutoff (PhysicalField.finiteSystem system)) output)
    (physicalOutputFiberAllSame
      (Audit.cutoff (PhysicalField.finiteSystem system)) output)


------------------------------------------------------------------------
-- Trust boundary.
------------------------------------------------------------------------

physicalCellRateSameObjectWeldClosed : Bool
physicalCellRateSameObjectWeldClosed = true

physicalCellRateDifferenceSameObjectWeldClosed : Bool
physicalCellRateDifferenceSameObjectWeldClosed = true

physicalRateDifferenceSameOutputFactorizationClosed : Bool
physicalRateDifferenceSameOutputFactorizationClosed = true

physicalOutputFibreSignedRateGeometryFactorizationClosed : Bool
physicalOutputFibreSignedRateGeometryFactorizationClosed = true

physicalCellRateDifferenceAddsSignClaim : Bool
physicalCellRateDifferenceAddsSignClaim = false

physicalCellRateDifferenceAddsQuantitativePayment : Bool
physicalCellRateDifferenceAddsQuantitativePayment = false

physicalCellRateDifferenceSameObjectWeldClosedIsTrue :
  physicalCellRateDifferenceSameObjectWeldClosed ≡ true
physicalCellRateDifferenceSameObjectWeldClosedIsTrue = refl

physicalRateDifferenceSameOutputFactorizationClosedIsTrue :
  physicalRateDifferenceSameOutputFactorizationClosed ≡ true
physicalRateDifferenceSameOutputFactorizationClosedIsTrue = refl

physicalOutputFibreSignedRateGeometryFactorizationClosedIsTrue :
  physicalOutputFibreSignedRateGeometryFactorizationClosed ≡ true
physicalOutputFibreSignedRateGeometryFactorizationClosedIsTrue = refl

physicalCellRateDifferenceAddsSignClaimIsFalse :
  physicalCellRateDifferenceAddsSignClaim ≡ false
physicalCellRateDifferenceAddsSignClaimIsFalse = refl

physicalCellRateDifferenceAddsQuantitativePaymentIsFalse :
  physicalCellRateDifferenceAddsQuantitativePayment ≡ false
physicalCellRateDifferenceAddsQuantitativePaymentIsFalse = refl
