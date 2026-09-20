module DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredInputLaplacianBonyVectorExact where

------------------------------------------------------------------------
-- PERIODIC B / CENTERED INPUT-LAPLACIAN RESIDUAL -> EXACT BONY VECTORS
--
-- IMPORTANT: centering remains GLOBAL while the physical incidence is routed.
--
-- For one literal fixed-output fibre F_k, write
--
--   n      = |F_k|,
--   S_tau  = |p_tau|^2 + |q_tau|^2,
--   S_tot  = sum_{tau in F_k} S_tau,
--   A_tau  = u^+_{p_tau} x u^-_{q_tau}.
--
-- The centered input-Laplacian residual is
--
--   R_S(A) = n sum S_tau A_tau - S_tot sum A_tau.
--
-- Define the globally-centered cell
--
--   C_tau = n S_tau A_tau - S_tot A_tau.
--
-- Then R_S(A) = sum C_tau exactly.  R581 can therefore route C_tau, without
-- re-centering any class, into LH / HL / HH->low / comparable vectors.
--
-- This gives a literal Complex3 equality BEFORE Hermitian observation:
--
--   R_S(A) = R_LH + R_HL + R_HH + R_CC.
--
-- We also merge LH+HL into one far-low vector:
--
--   R_S(A) = R_FL + R_HH + R_CC.
--
-- No norm, absolute value, class cardinality, Cauchy/Young/Schur estimate,
-- local class average, or cutoff-dependent constant is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredInputLaplacianVectorResidualExact as Input
import DASHI.Physics.Closure.NSTriadKNLiteralFourSignBonyRoutingRound581Exact as R581
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Generic rational scale/fold linearity.
------------------------------------------------------------------------

realScaleAdd :
  (scalar : ℚ) →
  (left right : C3.Complex3 F) →
  R291.realScale scalar (C3.complex3Add left right)
  ≡ C3.complex3Add
      (R291.realScale scalar left)
      (R291.realScale scalar right)
realScaleAdd scalar
    (C3.complex3
      (C3.complex lr li) (C3.complex mr mi) (C3.complex nr ni))
    (C3.complex3
      (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci)) =
  Algebra.complex3Ext
    (Algebra.complexExt
      (solve (scalar ∷ lr ∷ li ∷ ar ∷ ai ∷ []))
      (solve (scalar ∷ lr ∷ li ∷ ar ∷ ai ∷ [])))
    (Algebra.complexExt
      (solve (scalar ∷ mr ∷ mi ∷ br ∷ bi ∷ []))
      (solve (scalar ∷ mr ∷ mi ∷ br ∷ bi ∷ [])))
    (Algebra.complexExt
      (solve (scalar ∷ nr ∷ ni ∷ cr ∷ ci ∷ []))
      (solve (scalar ∷ nr ∷ ni ∷ cr ∷ ci ∷ [])))

realScaleZero :
  (scalar : ℚ) →
  R291.realScale scalar (C3.complex3Zero F)
  ≡ C3.complex3Zero F
realScaleZero scalar =
  Algebra.complex3Ext
    (Algebra.complexExt (solve (scalar ∷ [])) (solve (scalar ∷ [])))
    (Algebra.complexExt (solve (scalar ∷ [])) (solve (scalar ∷ [])))
    (Algebra.complexExt (solve (scalar ∷ [])) (solve (scalar ∷ [])))

realScaleProduct :
  (left right : ℚ) →
  (value : C3.Complex3 F) →
  R291.realScale left (R291.realScale right value)
  ≡ R291.realScale (left * right) value
realScaleProduct left right
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  Algebra.complex3Ext
    (Algebra.complexExt
      (solve (left ∷ right ∷ xr ∷ xi ∷ []))
      (solve (left ∷ right ∷ xr ∷ xi ∷ [])))
    (Algebra.complexExt
      (solve (left ∷ right ∷ yr ∷ yi ∷ []))
      (solve (left ∷ right ∷ yr ∷ yi ∷ [])))
    (Algebra.complexExt
      (solve (left ∷ right ∷ zr ∷ zi ∷ []))
      (solve (left ∷ right ∷ zr ∷ zi ∷ [])))

foldRealScale :
  (scalar : ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector (λ tau → R291.realScale scalar (value tau)) items
  ≡ R291.realScale scalar (R224.foldVector value items)
foldRealScale scalar value [] =
  sym (realScaleZero scalar)
foldRealScale scalar value (tau ∷ rest) =
  trans
    (cong
      (C3.complex3Add (R291.realScale scalar (value tau)))
      (foldRealScale scalar value rest))
    (sym
      (realScaleAdd scalar
        (value tau)
        (R224.foldVector value rest)))

------------------------------------------------------------------------
-- Global centered cell and exact fold meaning.
------------------------------------------------------------------------

centeredCell :
  (n total : ℚ) →
  (multiplier : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
centeredCell n total multiplier value tau =
  C3.complex3Add
    (R291.realScale n
      (R291.realScale (multiplier tau) (value tau)))
    (R291.realScale (0ℚ - total) (value tau))

foldCenteredCell :
  (n total : ℚ) →
  (multiplier : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector (centeredCell n total multiplier value) items
  ≡
  C3.complex3Add
    (R291.realScale n (Vector.weightedVectorSum multiplier value items))
    (R291.realScale (0ℚ - total) (R224.foldVector value items))
foldCenteredCell n total multiplier value items =
  trans
    (R225.foldPointwiseAdd
      (λ tau →
        R291.realScale n
          (R291.realScale (multiplier tau) (value tau)))
      (λ tau →
        R291.realScale (0ℚ - total) (value tau))
      items)
    (cong₂ C3.complex3Add firstMeaning secondMeaning)
  where
  firstMeaning :
    R224.foldVector
      (λ tau →
        R291.realScale n
          (R291.realScale (multiplier tau) (value tau)))
      items
    ≡
    R291.realScale n (Vector.weightedVectorSum multiplier value items)
  firstMeaning =
    trans
      (foldRealScale n
        (λ tau → R291.realScale (multiplier tau) (value tau))
        items)
      refl

  secondMeaning :
    R224.foldVector
      (λ tau → R291.realScale (0ℚ - total) (value tau))
      items
    ≡
    R291.realScale (0ℚ - total) (R224.foldVector value items)
  secondMeaning =
    foldRealScale (0ℚ - total) value items

centeredResidualIsCenteredCellFold :
  (multiplier : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  let
    n = Pair.natAsRational (length items)
    total = Pair.rateSum multiplier items
  in
  Vector.centeredMultiplierResidual multiplier value items
  ≡
  R224.foldVector (centeredCell n total multiplier value) items
centeredResidualIsCenteredCellFold multiplier value items =
  sym
    (foldCenteredCell
      (Pair.natAsRational (length items))
      (Pair.rateSum multiplier items)
      multiplier value items)

------------------------------------------------------------------------
-- Literal physical fixed-output input-Laplacian specialization.
------------------------------------------------------------------------

module FixedOutputBony
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat)
    (output : Z3.FourierMode) where

  items : List Physical.PhysicalTriadIncidence
  items = Output.physicalOutputFiber cutoff output

  multiplier : Physical.PhysicalTriadIncidence → ℚ
  multiplier = Input.inputMultiplier I

  value : Physical.PhysicalTriadIncidence → C3.Complex3 F
  value = R224.mixedPlusMinus S velocity

  n : ℚ
  n = Pair.natAsRational (length items)

  totalInputMass : ℚ
  totalInputMass = Pair.rateSum multiplier items

  globallyCenteredCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  globallyCenteredCell =
    centeredCell n totalInputMass multiplier value

  centeredResidual : C3.Complex3 F
  centeredResidual =
    Vector.centeredMultiplierResidual multiplier value items

  lowHighResidual highLowResidual highHighResidual comparableResidual :
    C3.Complex3 F
  lowHighResidual =
    R224.foldVector (R581.lowHighCell581 globallyCenteredCell) items
  highLowResidual =
    R224.foldVector (R581.highLowCell581 globallyCenteredCell) items
  highHighResidual =
    R224.foldVector (R581.highHighToLowCell581 globallyCenteredCell) items
  comparableResidual =
    R224.foldVector (R581.comparableCell581 globallyCenteredCell) items

  farLowResidual : C3.Complex3 F
  farLowResidual =
    C3.complex3Add lowHighResidual highLowResidual

  threeClassResidual : C3.Complex3 F
  threeClassResidual =
    C3.complex3Add
      farLowResidual
      (C3.complex3Add highHighResidual comparableResidual)

  centeredResidualIsFourBonyClasses :
    centeredResidual
    ≡ R576.fourVectorTotal
        lowHighResidual highLowResidual
        highHighResidual comparableResidual
  centeredResidualIsFourBonyClasses =
    trans
      (centeredResidualIsCenteredCellFold multiplier value items)
      (R581.literalFoldToFourClassFolds581 globallyCenteredCell items)

  fourBonyClassesAreThreeClasses :
    R576.fourVectorTotal
      lowHighResidual highLowResidual
      highHighResidual comparableResidual
    ≡ threeClassResidual
  fourBonyClassesAreThreeClasses =
    let
      lh = lowHighResidual
      hl = highLowResidual
      hh = highHighResidual
      cc = comparableResidual
    in
    Algebra.complex3Ext
      (coordinate lh hl hh cc C3.x)
      (coordinate lh hl hh cc C3.y)
      (coordinate lh hl hh cc C3.z)
    where
    coordinate :
      (lh hl hh cc : C3.Complex3 F) →
      (C3.Complex3 F → C3.Complex F) →
      C3.Complex F
      ≡ C3.Complex F
    coordinate lh hl hh cc projection = refl

  centeredResidualIsThreeBonyClasses :
    centeredResidual ≡ threeClassResidual
  centeredResidualIsThreeBonyClasses =
    trans centeredResidualIsFourBonyClasses
      fourBonyClassesAreThreeClasses

centeredInputLaplacianFourClassVectorSplitClosed : Bool
centeredInputLaplacianFourClassVectorSplitClosed = true

centeredInputLaplacianThreeClassVectorSplitClosed : Bool
centeredInputLaplacianThreeClassVectorSplitClosed = true

classLocalRecenteringIntroduced : Bool
classLocalRecenteringIntroduced = false

normIntroducedBeforeBonySplit : Bool
normIntroducedBeforeBonySplit = false

absoluteValueIntroducedBeforeBonySplit : Bool
absoluteValueIntroducedBeforeBonySplit = false

deepFarLowCenteredSignedPaymentClosedHere : Bool
deepFarLowCenteredSignedPaymentClosedHere = false

deepHighHighCenteredSignedPaymentClosedHere : Bool
deepHighHighCenteredSignedPaymentClosedHere = false

criticalCoreCenteredSignedPaymentClosedHere : Bool
criticalCoreCenteredSignedPaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

centeredInputLaplacianThreeClassVectorSplitClosedIsTrue :
  centeredInputLaplacianThreeClassVectorSplitClosed ≡ true
centeredInputLaplacianThreeClassVectorSplitClosedIsTrue = refl

classLocalRecenteringIntroducedIsFalse :
  classLocalRecenteringIntroduced ≡ false
classLocalRecenteringIntroducedIsFalse = refl
