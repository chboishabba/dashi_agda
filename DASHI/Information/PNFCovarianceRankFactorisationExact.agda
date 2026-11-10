module DASHI.Information.PNFCovarianceRankFactorisationExact where

-- A selected *centred* n×p covariance operator factors through
-- exactly n−1 tail-observation coordinates, independent of the scale.
-- No abstract rank/Nat field is taken as an assumption.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFFiniteCovarianceEconomicsExact as Matrix
import DASHI.Information.PNFCentredCovarianceExact as Centre
import DASHI.Information.PNFSampleMeanExact as Mean
import DASHI.Information.PNFCentredRankFactorisationExact as Factor
import DASHI.Information.PNFCentredLinearRankExact as Linear
import DASHI.Information.PNFCovarianceQuadraticIdentityExact as Quadratic

private
  SOf : Ring.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Ring.orderedScalar K)

covarianceAction :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k p : Nat} → (M : Mean.ActualFiniteMean K (suc k) p) →
  (scale : SOf K) → (Fin p → SOf K) → Fin p → SOf K
covarianceAction K M scale v i =
  Ring.sumFin (Ring.orderedScalar K)
    (λ j → Scalar._*_ (Ring.orderedScalar K)
      (Centre.scaledCovariance K (Mean.source M) scale i j)
      (v j))

-- A concrete map from the n−1 tail sample responses to p covariance
-- coordinates. This is the operator-level compression decoder.
covarianceFromTail :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k p : Nat} → (M : Mean.ActualFiniteMean K (suc k) p) →
  (scale : SOf K) → (Fin k → SOf K) → Fin p → SOf K
covarianceFromTail K M scale tail i =
  let S = Ring.orderedScalar K
      Y = Centre.centredMatrix K (Mean.source M)
  in
  Scalar._*_ S scale
    (Ring.sumFin S (λ r →
      Scalar._*_ S (Matrix.entry Y r i)
        (Factor.reconstructZeroSum K tail r)))

-- v ↦ C v equals (v ↦ tail(Xv)) followed by the explicit decoder.
-- Thus C factors through the (n−1)-coordinate carrier.
covarianceActionFactorsThroughTail :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k p : Nat} → (M : Mean.ActualFiniteMean K (suc k) p) →
  (scale : SOf K) → (v : Fin p → SOf K) → (i : Fin p) →
  covarianceAction K M scale v i ≡
  covarianceFromTail K M scale (Linear.tailAction K M v) i
covarianceActionFactorsThroughTail K M scale v i =
  let S = Ring.orderedScalar K
      Y = Centre.centredMatrix K (Mean.source M)
      projection = λ r → Ring.sumFin S
        (λ j → Scalar._*_ S (Matrix.entry Y r j) (v j))
  in
  trans
    (Ring.sumFinCong S
      (λ j → Ring.mulAssociative K scale (Matrix.gram K Y i j) (v j)))
    (trans
      (Ring.sumFinMulLeft K scale
        (λ j → Scalar._*_ S (Matrix.gram K Y i j) (v j)))
      (cong (Scalar._*_ S scale)
        (trans
          (Quadratic.gramActionEqualsRowProjection K Y v i)
          (Ring.sumFinCong S
            (λ r → cong (Scalar._*_ S (Matrix.entry Y r i))
              (trans
                (Ring.sumFinCong S
                  (λ j → Ring.mulCommutative K
                    (Matrix.entry Y r j) (v j)))
                (sym (Linear.centredActionFactorsThroughTail K M v r))))))))
