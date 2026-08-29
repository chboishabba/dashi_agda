module DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact where

------------------------------------------------------------------------
-- ROUND178 / RATIONAL LOW-OUTPUT MASS BOUND FOR THE RAW p/q CURL KERNEL
--
-- Round176 gives, on a resonant divergence-free pair,
--
--   K = u_p (k.u_q) + u_q (u_p.k) - k (u_p.u_q).
--
-- Each of the three vector terms has squared norm at most
--
--   |k|^2 ||u_p||^2 ||u_q||^2.
--
-- A finite three-term Cauchy estimate therefore gives the radical-free bound
--
--   ||K||^2 <= 9 |k|^2 ||u_p||^2 ||u_q||^2.
--
-- The constant is deliberately crude.  The decisive fact is that the ONLY
-- frequency in the majorant is the literal low output |k|^2: there is no
-- high-leg frequency and no convolution-fibre/cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRationalComplex3HermitianCauchyRound74Exact as HC
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNPressureHessianOrderedTermRationalBoundRound85Exact as R85
import DASHI.Physics.Closure.NSTriadKNRawCurlOutputDefectFactorizationRound176Exact as R176

F : C3.RealField _
F = Rational.rationalRealField

three nine : ℚ
three = 1ℚ + (1ℚ + 1ℚ)
nine = three * three

oneNN : 0ℚ ≤ 1ℚ
oneNN =
  subst
    (0ℚ ≤_)
    (solve [])
    (Separation.complexModulusSquaredNonnegative (C3.complex 1ℚ 0ℚ))

threeNN : 0ℚ ≤ three
threeNN = Rational.addNonnegative oneNN (Rational.addNonnegative oneNN oneNN)

ones : C3.Complex3 F
ones = C3.complex3
  (C3.complex 1ℚ 0ℚ)
  (C3.complex 1ℚ 0ℚ)
  (C3.complex 1ℚ 0ℚ)

onesNormSquaredIsThree : L2.complex3NormSquared ones ≡ three
onesNormSquaredIsThree = solve []

threeComplexSumModulusBound :
  (a b c : C3.Complex F) →
  L2.complexModulusSquared (C3.complexAdd (C3.complexAdd a b) c)
  ≤ three *
      (L2.complexModulusSquared a
       + L2.complexModulusSquared b
       + L2.complexModulusSquared c)
threeComplexSumModulusBound a b c =
  let
    terms = C3.complex3 a b c
    base = HC.rationalComplex3HermitianCauchy ones terms

    pairingMeaning :
      C3.hermitianPairing3 ones terms
      ≡ C3.complexAdd (C3.complexAdd a b) c
    pairingMeaning with a | b | c
    ... | C3.complex ar ai | C3.complex br bi | C3.complex cr ci =
      C3.complexExt (solve (ar ∷ br ∷ cr ∷ [])) (solve (ai ∷ bi ∷ ci ∷ []))

    termsMeaning :
      L2.complex3NormSquared terms
      ≡ L2.complexModulusSquared a
        + L2.complexModulusSquared b
        + L2.complexModulusSquared c
    termsMeaning = refl
  in
  subst
    (λ lower → lower ≤ three *
      (L2.complexModulusSquared a
       + L2.complexModulusSquared b
       + L2.complexModulusSquared c))
    (cong L2.complexModulusSquared pairingMeaning)
    (subst
      (λ upper →
        L2.complexModulusSquared (C3.hermitianPairing3 ones terms) ≤ upper)
      (trans
        (cong (λ x → x * L2.complex3NormSquared terms) onesNormSquaredIsThree)
        (cong (three *_) termsMeaning))
      base)

threeVectorSumNormSquaredBound :
  (u v w : C3.Complex3 F) →
  L2.complex3NormSquared (C3.complex3Add (C3.complex3Add u v) w)
  ≤ three *
      (L2.complex3NormSquared u
       + L2.complex3NormSquared v
       + L2.complex3NormSquared w)
threeVectorSumNormSquaredBound
    (C3.complex3 ux uy uz)
    (C3.complex3 vx vy vz)
    (C3.complex3 wx wy wz) =
  let
    bx = threeComplexSumModulusBound ux vx wx
    by = threeComplexSumModulusBound uy vy wy
    bz = threeComplexSumModulusBound uz vz wz
    added = ℚP.+-mono-≤ (ℚP.+-mono-≤ bx by) bz
    rearrange :
      three * (L2.complexModulusSquared ux + L2.complexModulusSquared vx + L2.complexModulusSquared wx)
      + three * (L2.complexModulusSquared uy + L2.complexModulusSquared vy + L2.complexModulusSquared wy)
      + three * (L2.complexModulusSquared uz + L2.complexModulusSquared vz + L2.complexModulusSquared wz)
      ≡
      three *
        (L2.complex3NormSquared (C3.complex3 ux uy uz)
         + L2.complex3NormSquared (C3.complex3 vx vy vz)
         + L2.complex3NormSquared (C3.complex3 wx wy wz))
    rearrange = solve
      ( L2.complexModulusSquared ux ∷ L2.complexModulusSquared uy ∷ L2.complexModulusSquared uz
      ∷ L2.complexModulusSquared vx ∷ L2.complexModulusSquared vy ∷ L2.complexModulusSquared vz
      ∷ L2.complexModulusSquared wx ∷ L2.complexModulusSquared wy ∷ L2.complexModulusSquared wz ∷ [])
  in
  subst
    (λ upper →
      L2.complex3NormSquared
        (C3.complex3Add
          (C3.complex3Add
            (C3.complex3 ux uy uz) (C3.complex3 vx vy vz))
          (C3.complex3 wx wy wz)) ≤ upper)
    rearrange added

scaleVectorMassBound :
  (scalar : C3.Complex F) (value : C3.Complex3 F)
  (scalarUpper valueMass upper : ℚ) →
  L2.complexModulusSquared scalar ≤ scalarUpper →
  L2.complex3NormSquared value ≡ valueMass →
  0ℚ ≤ scalarUpper → 0ℚ ≤ valueMass →
  scalarUpper * valueMass ≤ upper →
  L2.complex3NormSquared (C3.complex3Scale scalar value) ≤ upper
scaleVectorMassBound scalar value scalarUpper valueMass upper scalarBound valueMeaning scalarUpperNN valueNN endpoint =
  let
    scalarNN = Separation.complexModulusSquaredNonnegative scalar
    productBound = Rational.nonnegativeProductMonotone
      scalarNN valueNN scalarUpperNN valueNN scalarBound ℚP.≤-refl
  in
  ℚP.≤-trans
    (subst
      (λ left → left ≤ scalarUpper * valueMass)
      (R85.complex3ScaleNormSquared scalar value)
      (subst
        (λ right → L2.complexModulusSquared scalar * right ≤ scalarUpper * valueMass)
        valueMeaning productBound))
    endpoint

rawLowOutputKernelMassBound :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  {p q k : Z3.FourierMode}
  (uP uQ : C3.Complex3 F) →
  Z3.Resonance p q k →
  Helical.Transverse E p uP →
  Helical.Transverse E q uQ →
  L2.complex3NormSquared
    (R145.slotKernel (C3.modeVector E p) (C3.modeVector E q) uP uQ)
  ≤ nine * C3.normSquared I k
      * L2.complex3NormSquared uP
      * L2.complex3NormSquared uQ
rawLowOutputKernelMassBound E I {p} {q} {k} uP uQ resonance pTrans qTrans =
  let
    waveK = C3.modeVector E k
    eP = L2.complex3NormSquared uP
    eQ = L2.complex3NormSquared uQ
    k2 = C3.normSquared I k
    base = k2 * eP * eQ

    alpha = C3.bilinearDot3 waveK uQ
    beta  = C3.bilinearDot3 uP waveK
    gamma = C3.bilinearDot3 uP uQ

    x = C3.complex3Scale alpha uP
    y = C3.complex3Scale beta uQ
    z = C3.complex3Negate (C3.complex3Scale gamma waveK)

    alphaBound : L2.complexModulusSquared alpha ≤ k2 * eQ
    alphaBound =
      subst
        (λ left → left ≤ k2 * eQ)
        (cong L2.complexModulusSquared
          (sym (Hermitian.realModePairingIsBilinear E k uQ)))
        (subst
          (λ upper →
            L2.complexModulusSquared (C3.hermitianPairing3 waveK uQ) ≤ upper)
          (trans
            (cong (λ left → left * eQ) (R96.modeVectorNormSquaredMeaning E I k))
            (ℚP.*-comm k2 eQ))
          (HC.rationalComplex3HermitianCauchy waveK uQ))

    betaBound0 = R96.rationalBilinearDotCauchy uP waveK
    betaBound : L2.complexModulusSquared beta ≤ k2 * eP
    betaBound =
      subst
        (λ upper → L2.complexModulusSquared beta ≤ upper)
        (trans
          (cong (eP *_) (R96.modeVectorNormSquaredMeaning E I k))
          (ℚP.*-comm eP k2))
        betaBound0

    gammaBound : L2.complexModulusSquared gamma ≤ eP * eQ
    gammaBound = R96.rationalBilinearDotCauchy uP uQ

    k2NN = Separation.complex3NormSquaredNonnegative waveK
    k2NN' : 0ℚ ≤ k2
    k2NN' = subst (0ℚ ≤_) (R96.modeVectorNormSquaredMeaning E I k) k2NN
    ePNN = Separation.complex3NormSquaredNonnegative uP
    eQNN = Separation.complex3NormSquaredNonnegative uQ

    xBound : L2.complex3NormSquared x ≤ base
    xBound =
      let
        upperNN = R96.productNonnegative k2NN' eQNN
        endpoint : (k2 * eQ) * eP ≤ base
        endpoint = subst (_≤ base) (solve (k2 ∷ eP ∷ eQ ∷ [])) ℚP.≤-refl
      in
      scaleVectorMassBound alpha uP (k2 * eQ) eP base
        alphaBound refl upperNN ePNN endpoint

    yBound : L2.complex3NormSquared y ≤ base
    yBound =
      let
        upperNN = R96.productNonnegative k2NN' ePNN
        endpoint : (k2 * eP) * eQ ≤ base
        endpoint = subst (_≤ base) (solve (k2 ∷ eP ∷ eQ ∷ [])) ℚP.≤-refl
      in
      scaleVectorMassBound beta uQ (k2 * eP) eQ base
        betaBound refl upperNN eQNN endpoint

    rawZ = C3.complex3Scale gamma waveK
    zNormMeaning : L2.complex3NormSquared z ≡ L2.complex3NormSquared rawZ
    zNormMeaning with rawZ
    ... | C3.complex3 zx zy zz
      rewrite R85.complexModulusNegate zx
            | R85.complexModulusNegate zy
            | R85.complexModulusNegate zz = refl

    zBoundRaw : L2.complex3NormSquared rawZ ≤ base
    zBoundRaw =
      let
        upperNN = R96.productNonnegative ePNN eQNN
        endpoint : (eP * eQ) * k2 ≤ base
        endpoint = subst (_≤ base) (solve (k2 ∷ eP ∷ eQ ∷ [])) ℚP.≤-refl
      in
      scaleVectorMassBound gamma waveK (eP * eQ) k2 base
        gammaBound (R96.modeVectorNormSquaredMeaning E I k)
        upperNN k2NN' endpoint

    zBound : L2.complex3NormSquared z ≤ base
    zBound = subst (_≤ base) zNormMeaning zBoundRaw

    sumBound = threeVectorSumNormSquaredBound x y z
    termsBound :
      L2.complex3NormSquared x + L2.complex3NormSquared y + L2.complex3NormSquared z
      ≤ base + base + base
    termsBound = ℚP.+-mono-≤ (ℚP.+-mono-≤ xBound yBound) zBound

    scaledTerms =
      let instance threeNNI = nonNegative threeNN
      in ℚP.*-monoˡ-≤-nonNeg three termsBound

    targetMeaning : three * (base + base + base)
      ≡ nine * k2 * eP * eQ
    targetMeaning = solve (k2 ∷ eP ∷ eQ ∷ [])

    kernelMeaning = R176.rawPQSlotKernelFactorsThroughLiteralOutput
      E uP uQ resonance pTrans qTrans

    expandedMeaning :
      C3.complex3Subtract
        (C3.complex3Add
          (C3.complex3Scale alpha uP)
          (C3.complex3Scale beta uQ))
        (C3.complex3Scale gamma waveK)
      ≡ C3.complex3Add (C3.complex3Add x y) z
    expandedMeaning = refl
  in
  subst
    (λ lower → lower ≤ nine * k2 * eP * eQ)
    (cong L2.complex3NormSquared
      (trans kernelMeaning expandedMeaning))
    (ℚP.≤-trans sumBound
      (subst
        (λ upper →
          L2.complex3NormSquared (C3.complex3Add (C3.complex3Add x y) z) ≤ upper)
        targetMeaning scaledTerms))

round178RawCurlLowOutputKernelMassBoundClosed : Bool
round178RawCurlLowOutputKernelMassBoundClosed = true

round178HighLegFrequencyAppearsInKernelBound : Bool
round178HighLegFrequencyAppearsInKernelBound = false

round178FibreCardinalityFactorAppears : Bool
round178FibreCardinalityFactorAppears = false

round178GlobalCriticalSummationClosed : Bool
round178GlobalCriticalSummationClosed = false

round178PackageAClosed : Bool
round178PackageAClosed = false

round178RawCurlLowOutputKernelMassBoundClosedIsTrue :
  round178RawCurlLowOutputKernelMassBoundClosed ≡ true
round178RawCurlLowOutputKernelMassBoundClosedIsTrue = refl

round178PackageAClosedIsFalse : round178PackageAClosed ≡ false
round178PackageAClosedIsFalse = refl
