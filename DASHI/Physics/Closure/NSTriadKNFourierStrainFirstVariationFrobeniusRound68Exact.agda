module DASHI.Physics.Closure.NSTriadKNFourierStrainFirstVariationFrobeniusRound68Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- DOI: 10.1080/03605309608821197.
--
-- ROUND 68 / QUANTITATIVE FIRST VARIATION
--
-- The exact Round68 physical strain first variation is
--
--   DS_k[h] = |k|^-2 L_k(h) + D(|k|^-2)[h] A_k.
--
-- This file supplies the first genuine low/high quantitative estimate for that
-- same object.  Elementary Frobenius algebra gives
--
--   || |k|^-2 L_k(h) ||_F^2 <= 4 |k|^-2 |h|^2 |omega|^2,
--   || D(|k|^-2)[h] A_k ||_F^2 <= 2 |k|^-2 |h|^2 |omega|^2.
--
-- Using ||X+Y||_F^2 <= 2(||X||_F^2+||Y||_F^2),
--
--   ||DS_k[h]||_F^2 <= 12 |k|^-2 |h|^2 |omega|^2.
--
-- Thus the Taylor derivative is quantitatively controlled by the literal
-- squared low/dominant ratio.  The remaining B step is to insert the exact
-- branchwise dyadic shell separation and normalized Gram geometry, rather than
-- postulating a multiplier difference bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain
import DASHI.Physics.Closure.NSTriadKNFourierStrainExactFiniteDifferenceRound68Exact as FD
import DASHI.Physics.Closure.NSTriadKNFourierStrainSecondOrderTaylorRound68Exact as Taylor
import DASHI.Physics.Closure.NSTriadKNFourierStrainFrobeniusBoundRound68Exact as Frob
import DASHI.Physics.Closure.NSTriadKNHHGoodCompactAnnularMatrixFrobeniusBoundRound68Exact as FrobNN

half two four six twelve : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1
four = Int.+ 4 / 1
six = Int.+ 6 / 1
twelve = Int.+ 12 / 1

symmetricOuter : V.Vector3 → V.Vector3 → Matrix.Matrix3
symmetricOuter (V.v3 ux uy uz) (V.v3 vx vy vz) =
  Matrix.matrix3
    (ux * vx + vx * ux)
    (ux * vy + vx * uy)
    (ux * vz + vx * uz)
    (uy * vx + vy * ux)
    (uy * vy + vy * uy)
    (uy * vz + vy * uz)
    (uz * vx + vz * ux)
    (uz * vy + vz * uy)
    (uz * vz + vz * uz)

symmetricOuterFrobeniusExact : ∀ u v →
  Frob.frobeniusSquared (symmetricOuter u v)
  ≡ two * V.normSquared u * V.normSquared v
    + two * L2.square (V.dot u v)
symmetricOuterFrobeniusExact
    (V.v3 ux uy uz) (V.v3 vx vy vz) =
  solve (ux ∷ uy ∷ uz ∷ vx ∷ vy ∷ vz ∷ [])

vectorCauchySquared : ∀ u v →
  L2.square (V.dot u v) ≤ V.normSquared u * V.normSquared v
vectorCauchySquared u v =
  let
    crossNN = Frob.normSquaredNonnegative (BS.cross u v)
    lagrange = BS.crossNormLagrange u v
    added :
      L2.square (V.dot u v) + 0ℚ
      ≤ L2.square (V.dot u v) + V.normSquared (BS.cross u v)
    added = ℚP.+-monoˡ-≤ (L2.square (V.dot u v)) crossNN
    rightMeaning :
      L2.square (V.dot u v) + V.normSquared (BS.cross u v)
      ≡ V.normSquared u * V.normSquared v
    rightMeaning = trans
      (cong (L2.square (V.dot u v) +_) lagrange)
      (solve
        (V.normSquared u ∷ V.normSquared v ∷ V.dot u v ∷ []))
  in
  subst
    (λ left → left ≤ V.normSquared u * V.normSquared v)
    (ℚP.+-identityʳ (L2.square (V.dot u v)))
    (subst
      (λ right → L2.square (V.dot u v) + 0ℚ ≤ right)
      rightMeaning added)

symmetricOuterFrobeniusBound : ∀ u v →
  Frob.frobeniusSquared (symmetricOuter u v)
  ≤ four * V.normSquared u * V.normSquared v
symmetricOuterFrobeniusBound u v =
  let
    dotBound = vectorCauchySquared u v
    twoNN : 0ℚ ≤ two
    twoNN = toWitness {a? = 0ℚ ℚP.≤? two} _
    scaledDot :
      two * L2.square (V.dot u v)
      ≤ two * (V.normSquared u * V.normSquared v)
    scaledDot =
      let instance twoNNI = nonNegative twoNN
      in ℚP.*-monoˡ-≤-nonNeg two dotBound
    combined :
      two * V.normSquared u * V.normSquared v
        + two * L2.square (V.dot u v)
      ≤ two * V.normSquared u * V.normSquared v
        + two * (V.normSquared u * V.normSquared v)
    combined = ℚP.+-monoˡ-≤
      (two * V.normSquared u * V.normSquared v) scaledDot
    endpoint :
      two * V.normSquared u * V.normSquared v
        + two * (V.normSquared u * V.normSquared v)
      ≡ four * V.normSquared u * V.normSquared v
    endpoint = solve (V.normSquared u ∷ V.normSquared v ∷ [])
  in
  subst
    (λ left → left ≤ four * V.normSquared u * V.normSquared v)
    (sym (symmetricOuterFrobeniusExact u v))
    (subst
      (λ right →
        two * V.normSquared u * V.normSquared v
          + two * L2.square (V.dot u v) ≤ right)
      endpoint combined)

matrixAddFrobeniusBound : ∀ left right →
  Frob.frobeniusSquared (FD.matrixAdd left right)
  ≤ two * (Frob.frobeniusSquared left + Frob.frobeniusSquared right)
matrixAddFrobeniusBound
    (Matrix.matrix3 l11 l12 l13 l21 l22 l23 l31 l32 l33)
    (Matrix.matrix3 r11 r12 r13 r21 r22 r23 r31 r32 r33) =
  let
    component : ∀ a b → L2.square (a + b) ≤ two * (L2.square a + L2.square b)
    component a b =
      let
        defectNN = L2.squareNonnegative (a - b)
        base : L2.square (a + b) + 0ℚ
          ≤ L2.square (a + b) + L2.square (a - b)
        base = ℚP.+-monoˡ-≤ (L2.square (a + b)) defectNN
        exact :
          L2.square (a + b) + L2.square (a - b)
          ≡ two * (L2.square a + L2.square b)
        exact = solve (a ∷ b ∷ [])
      in
      subst
        (λ left → left ≤ two * (L2.square a + L2.square b))
        (ℚP.+-identityʳ (L2.square (a + b)))
        (subst
          (λ right → L2.square (a + b) + 0ℚ ≤ right)
          exact base)

    c11 = component l11 r11
    c12 = component l12 r12
    c13 = component l13 r13
    c21 = component l21 r21
    c22 = component l22 r22
    c23 = component l23 r23
    c31 = component l31 r31
    c32 = component l32 r32
    c33 = component l33 r33
  in
  -- One ring-normalized aggregation of the nine component inequalities.
  ℚP.≤-trans
    (ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (ℚP.+-mono-≤
            (ℚP.+-mono-≤
              (ℚP.+-mono-≤
                (ℚP.+-mono-≤
                  (ℚP.+-mono-≤ c11 c12) c13) c21) c22) c23) c31) c32) c33)
    (subst
      (λ left → left ≤ two *
        (Frob.frobeniusSquared
          (Matrix.matrix3 l11 l12 l13 l21 l22 l23 l31 l32 l33)
        + Frob.frobeniusSquared
          (Matrix.matrix3 r11 r12 r13 r21 r22 r23 r31 r32 r33)))
      (solve
        (l11 ∷ l12 ∷ l13 ∷ l21 ∷ l22 ∷ l23 ∷ l31 ∷ l32 ∷ l33
          ∷ r11 ∷ r12 ∷ r13 ∷ r21 ∷ r22 ∷ r23 ∷ r31 ∷ r32 ∷ r33 ∷ []))
      ℚP.≤-refl)

angularLinearVariationAsSymmetricOuters : ∀ theta h omega →
  FD.angularLinearVariation theta h omega
  ≡ FD.matrixAdd
      (Strain.scaleMatrix (- half) (symmetricOuter theta (BS.cross h omega)))
      (Strain.scaleMatrix (- half) (symmetricOuter h (BS.cross theta omega)))
angularLinearVariationAsSymmetricOuters
    (V.v3 tx ty tz) (V.v3 hx hy hz) (V.v3 wx wy wz) =
  Matrix.matrixExt
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ half ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ half ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ half ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ half ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ half ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ half ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ half ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ half ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ half ∷ []))

halfSquare : L2.square (- half) ≡ Int.+ 1 / 4
halfSquare = solve []

angularLinearVariationFrobeniusBound : ∀ theta h omega →
  Frob.frobeniusSquared (FD.angularLinearVariation theta h omega)
  ≤ four * V.normSquared theta * V.normSquared h * V.normSquared omega
angularLinearVariationFrobeniusBound theta h omega =
  let
    left = Strain.scaleMatrix (- half) (symmetricOuter theta (BS.cross h omega))
    right = Strain.scaleMatrix (- half) (symmetricOuter h (BS.cross theta omega))
    addBound = matrixAddFrobeniusBound left right
    leftOuter = symmetricOuterFrobeniusBound theta (BS.cross h omega)
    rightOuter = symmetricOuterFrobeniusBound h (BS.cross theta omega)
    quarter : ℚ
    quarter = Int.+ 1 / 4
    quarterNN : 0ℚ ≤ quarter
    quarterNN = toWitness {a? = 0ℚ ℚP.≤? quarter} _
    leftScaled :
      Frob.frobeniusSquared left
      ≤ V.normSquared theta * V.normSquared h * V.normSquared omega
    leftScaled =
      let
        first = subst
          (λ lhs → lhs ≤ quarter * (four * V.normSquared theta *
            V.normSquared (BS.cross h omega)))
          (sym (Frob.frobeniusSquaredScale (- half)
            (symmetricOuter theta (BS.cross h omega))))
          (let instance qNNI = nonNegative quarterNN
           in ℚP.*-monoˡ-≤-nonNeg quarter leftOuter)
        crossBound = Frob.crossNormBelowProduct h omega
        factorNN = Frob.normSquaredNonnegative theta
        scaledCross :
          V.normSquared theta * V.normSquared (BS.cross h omega)
          ≤ V.normSquared theta * (V.normSquared h * V.normSquared omega)
        scaledCross =
          let instance factorNNI = nonNegative factorNN
          in ℚP.*-monoˡ-≤-nonNeg (V.normSquared theta) crossBound
      in
      ℚP.≤-trans
        (subst
          (λ upper → Frob.frobeniusSquared left ≤ upper)
          (solve (V.normSquared theta ∷ V.normSquared (BS.cross h omega) ∷ []))
          first)
        (subst
          (λ rightBound →
            V.normSquared theta * V.normSquared (BS.cross h omega) ≤ rightBound)
          (solve (V.normSquared theta ∷ V.normSquared h ∷ V.normSquared omega ∷ []))
          scaledCross)
    rightScaled :
      Frob.frobeniusSquared right
      ≤ V.normSquared theta * V.normSquared h * V.normSquared omega
    rightScaled =
      let
        first = subst
          (λ lhs → lhs ≤ quarter * (four * V.normSquared h *
            V.normSquared (BS.cross theta omega)))
          (sym (Frob.frobeniusSquaredScale (- half)
            (symmetricOuter h (BS.cross theta omega))))
          (let instance qNNI = nonNegative quarterNN
           in ℚP.*-monoˡ-≤-nonNeg quarter rightOuter)
        crossBound = Frob.crossNormBelowProduct theta omega
        factorNN = Frob.normSquaredNonnegative h
        scaledCross :
          V.normSquared h * V.normSquared (BS.cross theta omega)
          ≤ V.normSquared h * (V.normSquared theta * V.normSquared omega)
        scaledCross =
          let instance factorNNI = nonNegative factorNN
          in ℚP.*-monoˡ-≤-nonNeg (V.normSquared h) crossBound
      in
      ℚP.≤-trans
        (subst
          (λ upper → Frob.frobeniusSquared right ≤ upper)
          (solve (V.normSquared h ∷ V.normSquared (BS.cross theta omega) ∷ []))
          first)
        (subst
          (λ rightBound →
            V.normSquared h * V.normSquared (BS.cross theta omega) ≤ rightBound)
          (solve (V.normSquared theta ∷ V.normSquared h ∷ V.normSquared omega ∷ []))
          scaledCross)
    sumScaled = ℚP.+-mono-≤ leftScaled rightScaled
  in
  subst
    (λ leftMass → leftMass ≤
      four * V.normSquared theta * V.normSquared h * V.normSquared omega)
    (cong Frob.frobeniusSquared
      (sym (angularLinearVariationAsSymmetricOuters theta h omega)))
    (ℚP.≤-trans addBound
      (subst
        (λ upper →
          two * (Frob.frobeniusSquared left + Frob.frobeniusSquared right)
          ≤ upper)
        (solve (V.normSquared theta ∷ V.normSquared h ∷ V.normSquared omega ∷ []))
        (let
          target = V.normSquared theta * V.normSquared h * V.normSquared omega
          targetNN : 0ℚ ≤ target
          targetNN =
            let
              thNN = Frob.normSquaredNonnegative theta
              hNN = Frob.normSquaredNonnegative h
              oNN = Frob.normSquaredNonnegative omega
              thhNN =
                let instance
                  a = nonNegative thNN
                  b = nonNegative hNN
                  p = ℚP.nonNeg*nonNeg⇒nonNeg (V.normSquared theta) (V.normSquared h)
                in ℚP.nonNegative⁻¹ (V.normSquared theta * V.normSquared h)
            in
            let instance
              a = nonNegative thhNN
              b = nonNegative oNN
              p = ℚP.nonNeg*nonNeg⇒nonNeg
                (V.normSquared theta * V.normSquared h) (V.normSquared omega)
            in ℚP.nonNegative⁻¹ target
          twoNN : 0ℚ ≤ two
          twoNN = toWitness {a? = 0ℚ ℚP.≤? two} _
          sumBound :
            Frob.frobeniusSquared left + Frob.frobeniusSquared right
            ≤ target + target
          sumBound = sumScaled
        in
        let instance twoNNI = nonNegative twoNN
        in ℚP.*-monoˡ-≤-nonNeg two sumBound)))

scaledAngularLinearFrobeniusBound : ∀ modeData h omega →
  Frob.frobeniusSquared
    (Strain.scaleMatrix (V.inverseNormSquared modeData)
      (FD.angularLinearVariation (V.mode modeData) h omega))
  ≤ four * V.inverseNormSquared modeData
      * V.normSquared h * V.normSquared omega
scaledAngularLinearFrobeniusBound modeData h omega =
  let
    inv = V.inverseNormSquared modeData
    norm = V.normSquared (V.mode modeData)
    raw = angularLinearVariationFrobeniusBound (V.mode modeData) h omega
    invSqNN = L2.squareNonnegative inv
    scaled =
      let instance invNNI = nonNegative invSqNN
      in ℚP.*-monoˡ-≤-nonNeg (L2.square inv) raw
    endpoint :
      L2.square inv * (four * norm * V.normSquared h * V.normSquared omega)
      ≡ four * inv * V.normSquared h * V.normSquared omega
    endpoint = trans
      (solve (inv ∷ norm ∷ four ∷ V.normSquared h ∷ V.normSquared omega ∷ []))
      (trans
        (cong (λ law → four * inv * law * V.normSquared h * V.normSquared omega)
          (V.inverseLaw modeData))
        (solve (inv ∷ four ∷ V.normSquared h ∷ V.normSquared omega ∷ [])))
  in
  subst
    (λ left → left ≤ four * inv * V.normSquared h * V.normSquared omega)
    (sym (Frob.frobeniusSquaredScale inv
      (FD.angularLinearVariation (V.mode modeData) h omega)))
    (subst
      (λ right →
        L2.square inv * Frob.frobeniusSquared
          (FD.angularLinearVariation (V.mode modeData) h omega) ≤ right)
      endpoint scaled)

inverseFirstVariationAngularFrobeniusBound : ∀ modeData h omega →
  Frob.frobeniusSquared
    (Strain.scaleMatrix (Taylor.inverseFirstVariation modeData h)
      (DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact.angularStrain
        (V.mode modeData) omega))
  ≤ two * V.inverseNormSquared modeData
      * V.normSquared h * V.normSquared omega
inverseFirstVariationAngularFrobeniusBound modeData h omega =
  let
    import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as Angular
    inv = V.inverseNormSquared modeData
    norm = V.normSquared (V.mode modeData)
    dot = V.dot (V.mode modeData) h
    angular = Angular.angularStrain (V.mode modeData) omega
    dInv = Taylor.inverseFirstVariation modeData h
    dotBound = vectorCauchySquared (V.mode modeData) h
    angularBound = Frob.angularStrainFrobeniusBound (V.mode modeData) omega
    dInvSquareMeaning :
      L2.square dInv ≡ four * L2.square inv * L2.square inv * L2.square dot
    dInvSquareMeaning = solve (inv ∷ dot ∷ [])
    dInvSquareBound :
      L2.square dInv
      ≤ four * L2.square inv * L2.square inv * (norm * V.normSquared h)
    dInvSquareBound =
      subst
        (λ left → left ≤
          four * L2.square inv * L2.square inv * (norm * V.normSquared h))
        (sym dInvSquareMeaning)
        (let
          factor = four * L2.square inv * L2.square inv
          factorNN : 0ℚ ≤ factor
          factorNN =
            let
              fourNN : 0ℚ ≤ four
              fourNN = toWitness {a? = 0ℚ ℚP.≤? four} _
              invNN = L2.squareNonnegative inv
              first =
                let instance
                  a = nonNegative fourNN
                  b = nonNegative invNN
                  p = ℚP.nonNeg*nonNeg⇒nonNeg four (L2.square inv)
                in ℚP.nonNegative⁻¹ (four * L2.square inv)
            in
            let instance
              a = nonNegative first
              b = nonNegative invNN
              p = ℚP.nonNeg*nonNeg⇒nonNeg (four * L2.square inv) (L2.square inv)
            in ℚP.nonNegative⁻¹ factor
        in
        let instance fNNI = nonNegative factorNN
        in ℚP.*-monoˡ-≤-nonNeg factor dotBound)
    angularNN = FrobNN.frobeniusSquaredNonnegative angular
    productBound :
      L2.square dInv * Frob.frobeniusSquared angular
      ≤ (four * L2.square inv * L2.square inv * (norm * V.normSquared h))
        * (Frob.half * norm * (norm * V.normSquared omega))
    productBound =
      L2.nonnegativeProductMonotone
        (L2.squareNonnegative dInv) angularNN
        (let
          right = four * L2.square inv * L2.square inv * (norm * V.normSquared h)
          -- all factors are nonnegative; use its square/product shape through
          -- comparison target rather than introducing a new positivity API.
          in
          let
            fourNN : 0ℚ ≤ four
            fourNN = toWitness {a? = 0ℚ ℚP.≤? four} _
            invNN = L2.squareNonnegative inv
            normNN = Frob.normSquaredNonnegative (V.mode modeData)
            hNN = Frob.normSquaredNonnegative h
            nhNN =
              let instance a = nonNegative normNN; b = nonNegative hNN
                  p = ℚP.nonNeg*nonNeg⇒nonNeg norm (V.normSquared h)
              in ℚP.nonNegative⁻¹ (norm * V.normSquared h)
            fiNN =
              let instance a = nonNegative fourNN; b = nonNegative invNN
                  p = ℚP.nonNeg*nonNeg⇒nonNeg four (L2.square inv)
              in ℚP.nonNegative⁻¹ (four * L2.square inv)
            fiiNN =
              let instance a = nonNegative fiNN; b = nonNegative invNN
                  p = ℚP.nonNeg*nonNeg⇒nonNeg (four * L2.square inv) (L2.square inv)
              in ℚP.nonNegative⁻¹ (four * L2.square inv * L2.square inv)
          in
          let instance a = nonNegative fiiNN; b = nonNegative nhNN
              p = ℚP.nonNeg*nonNeg⇒nonNeg
                (four * L2.square inv * L2.square inv) (norm * V.normSquared h)
          in ℚP.nonNegative⁻¹ right)
        (let
          halfNN = Frob.halfNonnegative
          normNN = Frob.normSquaredNonnegative (V.mode modeData)
          omegaNN = Frob.normSquaredNonnegative omega
          hnNN =
            let instance a = nonNegative halfNN; b = nonNegative normNN
                p = ℚP.nonNeg*nonNeg⇒nonNeg Frob.half norm
            in ℚP.nonNegative⁻¹ (Frob.half * norm)
          noNN =
            let instance a = nonNegative normNN; b = nonNegative omegaNN
                p = ℚP.nonNeg*nonNeg⇒nonNeg norm (V.normSquared omega)
            in ℚP.nonNegative⁻¹ (norm * V.normSquared omega)
        in
        let instance a = nonNegative hnNN; b = nonNegative noNN
            p = ℚP.nonNeg*nonNeg⇒nonNeg (Frob.half * norm) (norm * V.normSquared omega)
        in ℚP.nonNegative⁻¹ (Frob.half * norm * (norm * V.normSquared omega)))
        dInvSquareBound angularBound
    endpoint :
      (four * L2.square inv * L2.square inv * (norm * V.normSquared h))
        * (Frob.half * norm * (norm * V.normSquared omega))
      ≡ two * inv * V.normSquared h * V.normSquared omega
    endpoint = trans
      (solve (inv ∷ norm ∷ four ∷ Frob.half
        ∷ V.normSquared h ∷ V.normSquared omega ∷ []))
      (trans
        (cong (λ law → two * inv * law * law * law
          * V.normSquared h * V.normSquared omega)
          (V.inverseLaw modeData))
        (solve (inv ∷ two ∷ V.normSquared h ∷ V.normSquared omega ∷ [])))
  in
  subst
    (λ left → left ≤ two * inv * V.normSquared h * V.normSquared omega)
    (sym (Frob.frobeniusSquaredScale dInv angular))
    (subst
      (λ right → L2.square dInv * Frob.frobeniusSquared angular ≤ right)
      endpoint productBound)

physicalStrainFirstVariationFrobeniusBound : ∀ modeData h omega →
  Frob.frobeniusSquared (Taylor.strainFirstVariation modeData h omega)
  ≤ twelve * V.inverseNormSquared modeData
      * V.normSquared h * V.normSquared omega
physicalStrainFirstVariationFrobeniusBound modeData h omega =
  let
    left = Strain.scaleMatrix (V.inverseNormSquared modeData)
      (FD.angularLinearVariation (V.mode modeData) h omega)
    right = Strain.scaleMatrix (Taylor.inverseFirstVariation modeData h)
      (DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact.angularStrain
        (V.mode modeData) omega)
    addBound = matrixAddFrobeniusBound left right
    leftBound = scaledAngularLinearFrobeniusBound modeData h omega
    rightBound = inverseFirstVariationAngularFrobeniusBound modeData h omega
    combined = ℚP.+-mono-≤ leftBound rightBound
    twoNN : 0ℚ ≤ two
    twoNN = toWitness {a? = 0ℚ ℚP.≤? two} _
    scaledCombined =
      let instance twoNNI = nonNegative twoNN
      in ℚP.*-monoˡ-≤-nonNeg two combined
    endpoint :
      two *
        (four * V.inverseNormSquared modeData * V.normSquared h * V.normSquared omega
        + two * V.inverseNormSquared modeData * V.normSquared h * V.normSquared omega)
      ≡ twelve * V.inverseNormSquared modeData * V.normSquared h * V.normSquared omega
    endpoint = solve
      (V.inverseNormSquared modeData ∷ V.normSquared h
        ∷ V.normSquared omega ∷ [])
  in
  ℚP.≤-trans addBound
    (subst
      (λ rightTarget →
        two * (Frob.frobeniusSquared left + Frob.frobeniusSquared right)
        ≤ rightTarget)
      endpoint scaledCombined)

round68PhysicalFirstVariationLowHighBound12 : Bool
round68PhysicalFirstVariationLowHighBound12 = true

round68PhysicalFirstVariationLowHighBound12IsTrue :
  round68PhysicalFirstVariationLowHighBound12 ≡ true
round68PhysicalFirstVariationLowHighBound12IsTrue = refl
