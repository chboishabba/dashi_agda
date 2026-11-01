module DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerMassRound187Exact where

------------------------------------------------------------------------
-- ROUND187 / LOW-OUTPUT MASS SURVIVES PHYSICAL PARTNER COMPRESSION
--
-- Round178 controls each ordered raw-curl cell by
--
--   ||K||² <= 9 |k|² E_p E_q.
--
-- Round186 makes the exact physical partner block `(K_pq , K_qp)` explicit.
-- Here we prove that compressing the two ordered representatives into one
-- partner cell preserves the decisive LOW-OUTPUT structure.  A deliberately
-- crude fixed two-cell Cauchy estimate gives
--
--   ||K_pq + K_qp||² <= 54 |k|² E_p E_q.
--
-- The constant is immaterial; it is universal.  In particular partner
-- compression introduces no fibre-cardinality, shell-count, or high-leg
-- frequency factor.  The only remaining possible loss is the Gram debt among
-- distinct compressed cells inside one Bony class.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerBonyRound186Exact as R186
import DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact as R181

F = R178.F

two six fiftyFour : ℚ
two = 1ℚ + 1ℚ
six = R178.three * two
fiftyFour = six * R178.nine

physicalRawCurlPartnerMassBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence}
    (H : R186.PhysicalRawCurlCellData system tau) →
  L2.complex3NormSquared
    (R181.pairCell (R186.physicalRawCurlPartnerBlock H))
  ≤ fiftyFour * C3.normSquared I (Physical.k tau)
      * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
      * L2.complex3NormSquared (Audit.velocity system (Physical.q tau))
physicalRawCurlPartnerMassBound
    {E = E} {I = I} {system = system} {tau = tau} H =
  let
    uP = Audit.velocity system (Physical.p tau)
    uQ = Audit.velocity system (Physical.q tau)
    k2 = C3.normSquared I (Physical.k tau)
    eP = L2.complex3NormSquared uP
    eQ = L2.complex3NormSquared uQ
    base = R178.nine * k2 * eP * eQ

    leftBound :
      L2.complex3NormSquared (R186.rawCurlCell H) ≤ base
    leftBound =
      R178.rawLowOutputKernelMassBound
        E I uP uQ
        (Physical.resonance tau)
        (R186.pTransverse H)
        (R186.qTransverse H)

    rightRaw =
      R178.rawLowOutputKernelMassBound
        E I uQ uP
        (Physical.resonance (Symmetry.swapTriad tau))
        (R186.qTransverse H)
        (R186.pTransverse H)

    rightBound :
      L2.complex3NormSquared (R186.rawCurlSwapCell H) ≤ base
    rightBound =
      subst
        (λ upper →
          L2.complex3NormSquared (R186.rawCurlSwapCell H) ≤ upper)
        (solve (k2 ∷ eP ∷ eQ ∷ []))
        rightRaw

    zero = C3.complex3Zero F
    zeroMass : L2.complex3NormSquared zero ≡ 0ℚ
    zeroMass = solve []

    rawThree =
      R178.threeVectorSumNormSquaredBound
        (R186.rawCurlCell H)
        (R186.rawCurlSwapCell H)
        zero

    pairThree :
      L2.complex3NormSquared
        (R181.pairCell (R186.physicalRawCurlPartnerBlock H))
      ≤ R178.three *
          (L2.complex3NormSquared (R186.rawCurlCell H)
           + L2.complex3NormSquared (R186.rawCurlSwapCell H)
           + 0ℚ)
    pairThree = subst
      (λ zMass →
        L2.complex3NormSquared
          (R181.pairCell (R186.physicalRawCurlPartnerBlock H))
        ≤ R178.three *
          (L2.complex3NormSquared (R186.rawCurlCell H)
           + L2.complex3NormSquared (R186.rawCurlSwapCell H)
           + zMass))
      zeroMass rawThree

    sumBounds :
      L2.complex3NormSquared (R186.rawCurlCell H)
        + L2.complex3NormSquared (R186.rawCurlSwapCell H)
        + 0ℚ
      ≤ base + base + 0ℚ
    sumBounds =
      ℚP.+-mono-≤ (ℚP.+-mono-≤ leftBound rightBound) ℚP.≤-refl

    scaled :
      R178.three *
        (L2.complex3NormSquared (R186.rawCurlCell H)
         + L2.complex3NormSquared (R186.rawCurlSwapCell H)
         + 0ℚ)
      ≤ R178.three * (base + base + 0ℚ)
    scaled =
      let instance threeNNI = nonNegative R178.threeNN
      in ℚP.*-monoˡ-≤-nonNeg R178.three sumBounds

    targetMeaning :
      R178.three * (base + base + 0ℚ)
      ≡ fiftyFour * k2 * eP * eQ
    targetMeaning = solve (k2 ∷ eP ∷ eQ ∷ [])
  in
  ℚP.≤-trans pairThree
    (subst
      (λ upper →
        R178.three *
          (L2.complex3NormSquared (R186.rawCurlCell H)
           + L2.complex3NormSquared (R186.rawCurlSwapCell H)
           + 0ℚ)
        ≤ upper)
      targetMeaning scaled)

round187PartnerCompressionPreservesLowOutputGain : Bool
round187PartnerCompressionPreservesLowOutputGain = true

round187PartnerCompressionIntroducesCardinalityFactor : Bool
round187PartnerCompressionIntroducesCardinalityFactor = false

round187WithinClassGramDebtStillRequired : Bool
round187WithinClassGramDebtStillRequired = true

round187PackageAClosed : Bool
round187PackageAClosed = false

round187ClayPromotion : Bool
round187ClayPromotion = false
