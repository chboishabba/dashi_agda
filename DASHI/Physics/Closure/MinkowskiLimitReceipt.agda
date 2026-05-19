module DASHI.Physics.Closure.MinkowskiLimitReceipt where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec)

import DASHI.Geometry.ConeTimeIsotropy as CTI
import DASHI.Geometry.Signature.HyperbolicFormZ as HFZ
import DASHI.Geometry.Signature31FromIntrinsicShellForcing as S31ISF
import DASHI.Physics.Signature31IntrinsicRootSystemB4Instance as B4

------------------------------------------------------------------------
-- GR flat-space receipt.
--
-- This records the exact flat Lorentzian/Minkowski surface already available
-- to the B4 intrinsic-signature lane.  It does not claim curved GR recovery,
-- Einstein equations, continuum limit, or matter/source coupling.

MinkowskiCarrier : Set
MinkowskiCarrier = HFZ.CausalCountsZ 3

minkowskiQuadratic : MinkowskiCarrier → ℤ
minkowskiQuadratic = HFZ.F (+ 1) (+ 1)

record CarrierQuadraticIsMinkowski : Set₁ where
  field
    Carrier :
      Set

    quadraticForm :
      Carrier → ℤ

    minkowskiNorm :
      Carrier → ℤ

    exactEquality :
      ∀ x → quadraticForm x ≡ minkowskiNorm x

    b4IntrinsicSignature :
      CTI.Signature

    signatureMatch31 :
      b4IntrinsicSignature ≡ CTI.sig31

    flatSpaceOnly :
      Set

    noEinsteinEquationClaim :
      Set

    noCurvedGRPromotion :
      Set

minkowskiLimitReceipt :
  CarrierQuadraticIsMinkowski
minkowskiLimitReceipt =
  record
    { Carrier =
        MinkowskiCarrier
    ; quadraticForm =
        minkowskiQuadratic
    ; minkowskiNorm =
        minkowskiQuadratic
    ; exactEquality =
        λ _ → refl
    ; b4IntrinsicSignature =
        S31ISF.signature31FromIntrinsic B4.b4IntrinsicCoreAxioms
    ; signatureMatch31 =
        S31ISF.signature31FromIntrinsicMatchesCTI
          B4.b4IntrinsicCoreAxioms
    ; flatSpaceOnly =
        ⊤
    ; noEinsteinEquationClaim =
        ⊤
    ; noCurvedGRPromotion =
        ⊤
    }

minkowskiLimitFlatWitness :
  CarrierQuadraticIsMinkowski.flatSpaceOnly minkowskiLimitReceipt
minkowskiLimitFlatWitness = tt

minkowskiLimitNoCurvedGRPromotion :
  CarrierQuadraticIsMinkowski.noCurvedGRPromotion minkowskiLimitReceipt
minkowskiLimitNoCurvedGRPromotion = tt
