module DASHI.Physics.Closure.NSTriadKNWaleffeNetworkForcingSquaredMajorantRound105Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result: finite-dimensional Cauchy--Schwarz inequality.
-- DOI: not applicable to the original nineteenth-century results.
--
-- ROUND105 / NETWORK-FORCING SQUARED MAJORANT
--
-- Round94's exact Waleffe amplitude forcing is the complex scalar
--
--   F_net
--     = <F_k,u_p x u_q>
--       + <u_k,F_p x u_q>
--       + <u_k,u_p x F_q>.
--
-- Round105 already proves the complex cross-product Lagrange contraction.
-- Applying Hermitian Cauchy to each term and once more to the three-component
-- vector of terms yields the radical-free exact estimate
--
--   (Re F_net)^2 <= 3 [
--       ||F_k||^2 ||u_p||^2 ||u_q||^2
--     + ||F_p||^2 ||u_k||^2 ||u_q||^2
--     + ||F_q||^2 ||u_k||^2 ||u_p||^2 ].
--
-- Thus the remaining phase-forcing theorem is not an opaque quartic scalar:
-- it descends to the ACTUAL Galerkin forcing norms and modal energy masses.
-- This is the correct interface for the repository's existing output-fibre,
-- Schur and convolution estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRationalComplex3HermitianCauchyRound74Exact as HC
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Tangent
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as Transfer
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeEnergyProductRound105Exact as Amp

F : C3.RealField _
F = Rational.rationalRealField

three : ℚ
three = 1ℚ + (1ℚ + 1ℚ)

threeNonnegative : 0ℚ ≤ three
threeNonnegative =
  let
    oneNN : 0ℚ ≤ 1ℚ
    oneNN = ℚP.<⇒≤ (ℚP.positive⁻¹ 1ℚ)
  in
  ℚP.+-mono-≤ oneNN (ℚP.+-mono-≤ oneNN oneNN)

termK termP termQ :
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
termK uK uP uQ fK fP fQ =
  C3.hermitianPairing3 fK (Cross.complex3Cross uP uQ)
termP uK uP uQ fK fP fQ =
  C3.hermitianPairing3 uK (Cross.complex3Cross fP uQ)
termQ uK uP uQ fK fP fQ =
  C3.hermitianPairing3 uK (Cross.complex3Cross uP fQ)

termVector :
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
termVector uK uP uQ fK fP fQ =
  C3.complex3
    (termK uK uP uQ fK fP fQ)
    (termP uK uP uQ fK fP fQ)
    (termQ uK uP uQ fK fP fQ)

ones : C3.Complex3 F
ones = C3.complex3
  (C3.complex 1ℚ 0ℚ)
  (C3.complex 1ℚ 0ℚ)
  (C3.complex 1ℚ 0ℚ)

onesNormSquaredIsThree : L2.complex3NormSquared ones ≡ three
onesNormSquaredIsThree = solve []

onesPairingIsNetworkForcing :
  (uK uP uQ fK fP fQ : C3.Complex3 F) →
  C3.hermitianPairing3 ones (termVector uK uP uQ fK fP fQ)
  ≡ Tangent.networkForcing uK uP uQ fK fP fQ
onesPairingIsNetworkForcing uK uP uQ fK fP fQ
  with termK uK uP uQ fK fP fQ
     | termP uK uP uQ fK fP fQ
     | termQ uK uP uQ fK fP fQ
... | C3.complex kr ki | C3.complex pr pi | C3.complex qr qi =
  C3.complexExt (solve (kr ∷ pr ∷ qr ∷ [])) (solve (ki ∷ pi ∷ qi ∷ []))

termVectorNormSquaredMeaning :
  (uK uP uQ fK fP fQ : C3.Complex3 F) →
  L2.complex3NormSquared (termVector uK uP uQ fK fP fQ)
  ≡
    L2.complexModulusSquared (termK uK uP uQ fK fP fQ)
    + L2.complexModulusSquared (termP uK uP uQ fK fP fQ)
    + L2.complexModulusSquared (termQ uK uP uQ fK fP fQ)
termVectorNormSquaredMeaning uK uP uQ fK fP fQ = refl

networkForcingModulusSquaredBelowThreeTermMass :
  (uK uP uQ fK fP fQ : C3.Complex3 F) →
  L2.complexModulusSquared (Tangent.networkForcing uK uP uQ fK fP fQ)
  ≤ three * L2.complex3NormSquared (termVector uK uP uQ fK fP fQ)
networkForcingModulusSquaredBelowThreeTermMass uK uP uQ fK fP fQ =
  let
    base = HC.rationalComplex3HermitianCauchy
      ones (termVector uK uP uQ fK fP fQ)
    lowerMeaning =
      cong L2.complexModulusSquared
        (onesPairingIsNetworkForcing uK uP uQ fK fP fQ)
    upperMeaning =
      cong
        (λ x → x * L2.complex3NormSquared (termVector uK uP uQ fK fP fQ))
        onesNormSquaredIsThree
  in
  subst
    (λ lower → lower ≤ three * L2.complex3NormSquared (termVector uK uP uQ fK fP fQ))
    lowerMeaning
    (subst
      (λ upper →
        L2.complexModulusSquared
          (C3.hermitianPairing3 ones (termVector uK uP uQ fK fP fQ))
        ≤ upper)
      upperMeaning base)

scaleRight : ∀ {a b c : ℚ} → 0ℚ ≤ a → b ≤ c → a * b ≤ a * c
scaleRight {a} aNN bound =
  let instance aNNI : NonNegative a
      aNNI = nonNegative aNN
  in ℚP.*-monoˡ-≤-nonNeg a bound

termKMassBound :
  (uP uQ fK : C3.Complex3 F) →
  L2.complexModulusSquared
    (C3.hermitianPairing3 fK (Cross.complex3Cross uP uQ))
  ≤ L2.complex3NormSquared fK
      * L2.complex3NormSquared uP
      * L2.complex3NormSquared uQ
termKMassBound uP uQ fK =
  let
    cross = Cross.complex3Cross uP uQ
    first = HC.rationalComplex3HermitianCauchy fK cross
    crossBound = Amp.crossNormSquaredBelowProduct uP uQ
    fNN = Separation.complex3NormSquaredNonnegative fK
    second = scaleRight fNN crossBound
    endpoint :
      L2.complex3NormSquared fK
        * (L2.complex3NormSquared uP * L2.complex3NormSquared uQ)
      ≡ L2.complex3NormSquared fK
          * L2.complex3NormSquared uP
          * L2.complex3NormSquared uQ
    endpoint = solve
      (L2.complex3NormSquared fK ∷ L2.complex3NormSquared uP
       ∷ L2.complex3NormSquared uQ ∷ [])
  in
  ℚP.≤-trans first (subst (λ upper →
    L2.complex3NormSquared fK * L2.complex3NormSquared cross ≤ upper)
    endpoint second)

termPMassBound :
  (uK uQ fP : C3.Complex3 F) →
  L2.complexModulusSquared
    (C3.hermitianPairing3 uK (Cross.complex3Cross fP uQ))
  ≤ L2.complex3NormSquared fP
      * L2.complex3NormSquared uK
      * L2.complex3NormSquared uQ
termPMassBound uK uQ fP =
  let
    cross = Cross.complex3Cross fP uQ
    first = HC.rationalComplex3HermitianCauchy uK cross
    crossBound = Amp.crossNormSquaredBelowProduct fP uQ
    kNN = Separation.complex3NormSquaredNonnegative uK
    second = scaleRight kNN crossBound
    endpoint :
      L2.complex3NormSquared uK
        * (L2.complex3NormSquared fP * L2.complex3NormSquared uQ)
      ≡ L2.complex3NormSquared fP
          * L2.complex3NormSquared uK
          * L2.complex3NormSquared uQ
    endpoint = solve
      (L2.complex3NormSquared uK ∷ L2.complex3NormSquared fP
       ∷ L2.complex3NormSquared uQ ∷ [])
  in
  ℚP.≤-trans first (subst (λ upper →
    L2.complex3NormSquared uK * L2.complex3NormSquared cross ≤ upper)
    endpoint second)

termQMassBound :
  (uK uP fQ : C3.Complex3 F) →
  L2.complexModulusSquared
    (C3.hermitianPairing3 uK (Cross.complex3Cross uP fQ))
  ≤ L2.complex3NormSquared fQ
      * L2.complex3NormSquared uK
      * L2.complex3NormSquared uP
termQMassBound uK uP fQ =
  let
    cross = Cross.complex3Cross uP fQ
    first = HC.rationalComplex3HermitianCauchy uK cross
    crossBound = Amp.crossNormSquaredBelowProduct uP fQ
    kNN = Separation.complex3NormSquaredNonnegative uK
    second = scaleRight kNN crossBound
    endpoint :
      L2.complex3NormSquared uK
        * (L2.complex3NormSquared uP * L2.complex3NormSquared fQ)
      ≡ L2.complex3NormSquared fQ
          * L2.complex3NormSquared uK
          * L2.complex3NormSquared uP
    endpoint = solve
      (L2.complex3NormSquared uK ∷ L2.complex3NormSquared uP
       ∷ L2.complex3NormSquared fQ ∷ [])
  in
  ℚP.≤-trans first (subst (λ upper →
    L2.complex3NormSquared uK * L2.complex3NormSquared cross ≤ upper)
    endpoint second)

networkForcingRealSquareMajorant :
  (uK uP uQ fK fP fQ : C3.Complex3 F) →
  C3.real (Tangent.networkForcing uK uP uQ fK fP fQ)
    * C3.real (Tangent.networkForcing uK uP uQ fK fP fQ)
  ≤ three *
    ( L2.complex3NormSquared fK * L2.complex3NormSquared uP * L2.complex3NormSquared uQ
    + L2.complex3NormSquared fP * L2.complex3NormSquared uK * L2.complex3NormSquared uQ
    + L2.complex3NormSquared fQ * L2.complex3NormSquared uK * L2.complex3NormSquared uP )
networkForcingRealSquareMajorant uK uP uQ fK fP fQ =
  let
    network = Tangent.networkForcing uK uP uQ fK fP fQ
    realBelow = Transfer.realCoordinateSquareBelowModulus network
    sumBelow = networkForcingModulusSquaredBelowThreeTermMass uK uP uQ fK fP fQ

    kBound = termKMassBound uP uQ fK
    pBound = termPMassBound uK uQ fP
    qBound = termQMassBound uK uP fQ
    termsBound = ℚP.+-mono-≤ (ℚP.+-mono-≤ kBound pBound) qBound

    scaledTerms =
      let instance threeNN : NonNegative three
          threeNN = nonNegative threeNonnegative
      in ℚP.*-monoˡ-≤-nonNeg three termsBound

    termMeaning = termVectorNormSquaredMeaning uK uP uQ fK fP fQ
  in
  ℚP.≤-trans realBelow
    (ℚP.≤-trans sumBelow
      (subst
        (λ left → left ≤ three *
          ( L2.complex3NormSquared fK * L2.complex3NormSquared uP * L2.complex3NormSquared uQ
          + L2.complex3NormSquared fP * L2.complex3NormSquared uK * L2.complex3NormSquared uQ
          + L2.complex3NormSquared fQ * L2.complex3NormSquared uK * L2.complex3NormSquared uP ))
        (cong (three *_) termMeaning)
        scaledTerms))

round105WaleffeNetworkForcingSquaredMajorantClosed : Bool
round105WaleffeNetworkForcingSquaredMajorantClosed = true

round105NetworkForcingReducedToPhysicalForcingNorms : Bool
round105NetworkForcingReducedToPhysicalForcingNorms = true

round105WaleffeNetworkForcingSquaredMajorantClosedIsTrue :
  round105WaleffeNetworkForcingSquaredMajorantClosed ≡ true
round105WaleffeNetworkForcingSquaredMajorantClosedIsTrue = refl

round105NetworkForcingReducedToPhysicalForcingNormsIsTrue :
  round105NetworkForcingReducedToPhysicalForcingNorms ≡ true
round105NetworkForcingReducedToPhysicalForcingNormsIsTrue = refl
