module DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredInputLaplacianVectorResidualExact where

------------------------------------------------------------------------
-- PERIODIC B / CENTERED-FREQUENCY RESIDUAL = 2 * INPUT-LAPLACIAN RESIDUAL
--
-- The scalar covariance owner already proves this after Hermitian observation.
-- The complete-graph vector identity now lets us prove it on the VECTOR itself.
--
-- On one fixed-output fibre p+q=k:
--
--   C_tau = |p-q|^2,
--   S_tau = |p|^2 + |q|^2,
--
-- and for every pair alpha,beta:
--
--   C_alpha - C_beta = 2 (S_alpha - S_beta).
--
-- Hence the literal pair-difference vectors satisfy
--
--   sum_{a<b} (C_a-C_b)(A_a-A_b)
--     = 2 sum_{a<b} (S_a-S_b)(A_a-A_b),
--
-- and, using the exact vector/residual weld on both sides,
--
--   centeredMultiplierResidual C
--     = 2 * centeredMultiplierResidual S.
--
-- No scalar observation, norm, absolute value, pair count, or cutoff factor
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact as Centered
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceVectorCenteringExact as PairVector
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceVectorResidualWeldExact as Weld
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector

F : C3.RealField _
F = Rational.rationalRealField

centeredMultiplier :
  (E : C3.IntegerEmbedding F) →
  Physical.PhysicalTriadIncidence → ℚ
centeredMultiplier E tau =
  Rate.centeredSquare E (Physical.p tau) (Physical.q tau)

inputMultiplier :
  ∀ {E : C3.IntegerEmbedding F} →
  (I : C3.ModeInverseSquare F E) →
  Physical.PhysicalTriadIncidence → ℚ
inputMultiplier I tau =
  Rate.inputSquareMass I (Physical.p tau) (Physical.q tau)

scaleTwo :
  C3.Complex3 F → C3.Complex3 F
scaleTwo value = R291.realScale Rate.two value

pairVectorTermCenteredIsTwiceInput :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  PairVector.pairVectorTerm (centeredMultiplier E) value alpha beta
  ≡
  scaleTwo
    (PairVector.pairVectorTerm (inputMultiplier I) value alpha beta)
pairVectorTermCenteredIsTwiceInput E I value alpha beta sameOutput =
  let
    cA = centeredMultiplier E alpha
    cB = centeredMultiplier E beta
    sA = inputMultiplier I alpha
    sB = inputMultiplier I beta
    dv = C3.complex3Subtract (value alpha) (value beta)

    scalar :
      cA - cB ≡ Rate.two * (sA - sB)
    scalar =
      sym (Rate.fixedOutputInputSquareDifference E I alpha beta sameOutput)
  in
  trans
    (cong (λ selected → R291.realScale selected dv) scalar)
    scaleProduct
  where
  scaleProduct :
    R291.realScale
      (Rate.two *
        (inputMultiplier I alpha - inputMultiplier I beta))
      (C3.complex3Subtract (value alpha) (value beta))
    ≡
    scaleTwo
      (R291.realScale
        (inputMultiplier I alpha - inputMultiplier I beta)
        (C3.complex3Subtract (value alpha) (value beta)))
  scaleProduct
    with C3.complex3Subtract (value alpha) (value beta)
  ... | C3.complex3
        (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi) =
    Algebra.complex3Ext
      (Algebra.complexExt
        (solve
          ( Rate.two
          ∷ inputMultiplier I alpha ∷ inputMultiplier I beta
          ∷ xr ∷ xi ∷ []))
        (solve
          ( Rate.two
          ∷ inputMultiplier I alpha ∷ inputMultiplier I beta
          ∷ xr ∷ xi ∷ [])))
      (Algebra.complexExt
        (solve
          ( Rate.two
          ∷ inputMultiplier I alpha ∷ inputMultiplier I beta
          ∷ yr ∷ yi ∷ []))
        (solve
          ( Rate.two
          ∷ inputMultiplier I alpha ∷ inputMultiplier I beta
          ∷ yr ∷ yi ∷ [])))
      (Algebra.complexExt
        (solve
          ( Rate.two
          ∷ inputMultiplier I alpha ∷ inputMultiplier I beta
          ∷ zr ∷ zi ∷ []))
        (solve
          ( Rate.two
          ∷ inputMultiplier I alpha ∷ inputMultiplier I beta
          ∷ zr ∷ zi ∷ [])))

pairAgainstHeadCenteredIsTwiceInput :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  {output : Z3.FourierMode} →
  (head : Physical.PhysicalTriadIncidence) →
  (rest : List Physical.PhysicalTriadIncidence) →
  Centered.OutputHomogeneous output (head ∷ rest) →
  PairVector.pairVectorAgainstHead
    (centeredMultiplier E) value head rest
  ≡
  scaleTwo
    (PairVector.pairVectorAgainstHead
      (inputMultiplier I) value head rest)
pairAgainstHeadCenteredIsTwiceInput E I value head [] homogeneous =
  zeroScale
  where
  zeroScale :
    C3.complex3Zero F ≡ scaleTwo (C3.complex3Zero F)
  zeroScale =
    Algebra.complex3Ext
      (Algebra.complexExt (solve (Rate.two ∷ [])) (solve (Rate.two ∷ [])))
      (Algebra.complexExt (solve (Rate.two ∷ [])) (solve (Rate.two ∷ [])))
      (Algebra.complexExt (solve (Rate.two ∷ [])) (solve (Rate.two ∷ [])))
pairAgainstHeadCenteredIsTwiceInput
    E I value {output} head (x ∷ xs) homogeneous =
  let
    sameOutput : Physical.k head ≡ Physical.k x
    sameOutput = Centered.pairSameOutput homogeneous x (Cube.here refl)

    headPart =
      pairVectorTermCenteredIsTwiceInput E I value head x sameOutput

    tailHom : Centered.OutputHomogeneous output (head ∷ xs)
    tailHom .head (Cube.here refl) =
      homogeneous head (Cube.here refl)
    tailHom tau (Cube.there member) =
      homogeneous tau (Cube.there (Cube.there member))

    tailPart =
      pairAgainstHeadCenteredIsTwiceInput
        E I value head xs tailHom
  in
  trans
    (cong₂ C3.complex3Add headPart tailPart)
    (sym
      (scaleTwoAdd
        (PairVector.pairVectorTerm (inputMultiplier I) value head x)
        (PairVector.pairVectorAgainstHead
          (inputMultiplier I) value head xs)))
  where
  scaleTwoAdd :
    (left right : C3.Complex3 F) →
    scaleTwo (C3.complex3Add left right)
    ≡ C3.complex3Add (scaleTwo left) (scaleTwo right)
  scaleTwoAdd
      (C3.complex3 lx ly lz)
      (C3.complex3 rx ry rz) =
    Algebra.complex3Ext
      (scaleComplexAdd lx rx)
      (scaleComplexAdd ly ry)
      (scaleComplexAdd lz rz)
    where
    scaleComplexAdd :
      (left right : C3.Complex F) →
      C3.complexMultiply
        (C3.realEmbed F Rate.two)
        (C3.complexAdd left right)
      ≡
      C3.complexAdd
        (C3.complexMultiply (C3.realEmbed F Rate.two) left)
        (C3.complexMultiply (C3.realEmbed F Rate.two) right)
    scaleComplexAdd
        (C3.complex lr li) (C3.complex rr ri) =
      Algebra.complexExt
        (solve (Rate.two ∷ lr ∷ li ∷ rr ∷ ri ∷ []))
        (solve (Rate.two ∷ lr ∷ li ∷ rr ∷ ri ∷ []))

pairVectorCenteredIsTwiceInput :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  {output : Z3.FourierMode} →
  (items : List Physical.PhysicalTriadIncidence) →
  Centered.OutputHomogeneous output items →
  PairVector.pairVectorDifferenceSum
    (centeredMultiplier E) value items
  ≡
  scaleTwo
    (PairVector.pairVectorDifferenceSum
      (inputMultiplier I) value items)
pairVectorCenteredIsTwiceInput E I value [] homogeneous =
  let
    zeroScale :
      C3.complex3Zero F ≡ scaleTwo (C3.complex3Zero F)
    zeroScale =
      Algebra.complex3Ext
        (Algebra.complexExt (solve (Rate.two ∷ [])) (solve (Rate.two ∷ [])))
        (Algebra.complexExt (solve (Rate.two ∷ [])) (solve (Rate.two ∷ [])))
        (Algebra.complexExt (solve (Rate.two ∷ [])) (solve (Rate.two ∷ [])))
  in zeroScale
pairVectorCenteredIsTwiceInput
    E I value {output} (head ∷ xs) homogeneous =
  let
    headPart =
      pairAgainstHeadCenteredIsTwiceInput
        E I value head xs homogeneous
    tailPart =
      pairVectorCenteredIsTwiceInput
        E I value xs (Centered.tailHomogeneous homogeneous)
  in
  trans
    (cong₂ C3.complex3Add headPart tailPart)
    (sym
      (scaleAdd
        (PairVector.pairVectorAgainstHead
          (inputMultiplier I) value head xs)
        (PairVector.pairVectorDifferenceSum
          (inputMultiplier I) value xs)))
  where
  scaleAdd :
    (left right : C3.Complex3 F) →
    scaleTwo (C3.complex3Add left right)
    ≡ C3.complex3Add (scaleTwo left) (scaleTwo right)
  scaleAdd
      (C3.complex3 lx ly lz)
      (C3.complex3 rx ry rz) =
    Algebra.complex3Ext
      (scaleComplexAdd lx rx)
      (scaleComplexAdd ly ry)
      (scaleComplexAdd lz rz)
    where
    scaleComplexAdd :
      (left right : C3.Complex F) →
      C3.complexMultiply
        (C3.realEmbed F Rate.two)
        (C3.complexAdd left right)
      ≡
      C3.complexAdd
        (C3.complexMultiply (C3.realEmbed F Rate.two) left)
        (C3.complexMultiply (C3.realEmbed F Rate.two) right)
    scaleComplexAdd
        (C3.complex lr li) (C3.complex rr ri) =
      Algebra.complexExt
        (solve (Rate.two ∷ lr ∷ li ∷ rr ∷ ri ∷ []))
        (solve (Rate.two ∷ lr ∷ li ∷ rr ∷ ri ∷ []))

literalFixedOutputCenteredResidualIsTwiceInputResidual :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  Vector.centeredMultiplierResidual
    (centeredMultiplier E) value
    (Output.physicalOutputFiber cutoff output)
  ≡
  scaleTwo
    (Vector.centeredMultiplierResidual
      (inputMultiplier I) value
      (Output.physicalOutputFiber cutoff output))
literalFixedOutputCenteredResidualIsTwiceInputResidual
    E I value cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    homogeneous = Centered.literalOutputFibreHomogeneous cutoff output

    centeredPair :
      PairVector.pairVectorDifferenceSum
        (centeredMultiplier E) value items
      ≡
      scaleTwo
        (PairVector.pairVectorDifferenceSum
          (inputMultiplier I) value items)
    centeredPair =
      pairVectorCenteredIsTwiceInput E I value items homogeneous

    centeredWeld =
      Weld.pairVectorDifferenceIsCenteredMultiplierResidual
        (centeredMultiplier E) value items

    inputWeld =
      Weld.pairVectorDifferenceIsCenteredMultiplierResidual
        (inputMultiplier I) value items
  in
  trans
    (sym centeredWeld)
    (trans centeredPair
      (cong scaleTwo inputWeld))

centeredInputLaplacianVectorIdentityClosed : Bool
centeredInputLaplacianVectorIdentityClosed = true

centeredInputLaplacianIdentityRequiresHermitianObservation : Bool
centeredInputLaplacianIdentityRequiresHermitianObservation = false

centeredInputLaplacianIdentityAddsCardinalityFactor : Bool
centeredInputLaplacianIdentityAddsCardinalityFactor = false

quantitativeInputLaplacianResidualPaymentClosedHere : Bool
quantitativeInputLaplacianResidualPaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

centeredInputLaplacianVectorIdentityClosedIsTrue :
  centeredInputLaplacianVectorIdentityClosed ≡ true
centeredInputLaplacianVectorIdentityClosedIsTrue = refl
