module DASHI.Reasoning.NullTriangleRamifiedSinglePrefixH05Exact where

-- Use the actual H05 observer and existing integral coefficient tower.
-- A ONE-trit prepend re-charts real/imaginary digit alignment. It is
-- not a uniformizer multiplication. Two aligned prepends give that step.
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Vec using (Vec)
import DASHI.Algebra.Trit as T
import DASHI.Algebra.TriadicFiniteMultiplicationCompatibleExact as A
import DASHI.Reasoning.NullTriangleNativeH05ObserverExact as H
import DASHI.Reasoning.NullTriangleNativePairedRefinementExact as Pair
import DASHI.Reasoning.NullTriangleRamifiedNativeTowerExact as K
import DASHI.Core.GovernedIndexedResidualCubeExact as Cube

refinedCoordinate : Vec T.Trit 10 → K.Ramified
refinedCoordinate v = K.decodeEven (Pair.packEven {5} v)

-- For z=A+iB with A,B in the ramified Eisenstein subalgebra,
-- prepend t sends z to t+pi*B+i*A. In the native (a+b*pi) chart
-- a=aR+i*aI, b=bR+i*bI, this has the following four coefficients.
singlePrefixCoefficient : T.Trit → K.Ramified → K.Ramified
singlePrefixCoefficient t (K.coefficients (K.gaussian aR aI) (K.gaussian bR bI)) =
  K.coefficients
    (K.gaussian (A.addLimit (K.digit t) (A.negateLimit (K.times3 bI))) aR)
    (K.gaussian (A.addLimit aI (A.negateLimit (K.times3 bI))) bR)

-- Actual source face observations. No new H05 action or carrier.
-- Source exact and residual faces are still H.exact and H.residual.
upperXY : ∀ o →
  K.observerCoordinate (H.yO (H.xO o)) ≡
  K.observerCoordinate (H.xO (H.yO o))
upperXY o = cong K.observerCoordinate (H.xyO o)

lowerXY : ∀ v →
  refinedCoordinate (H.y10 (H.x10 v)) ≡
  refinedCoordinate (H.x10 (H.y10 v))
lowerXY v = cong refinedCoordinate (H.xy10 v)

observedXZ : ∀ t o →
  refinedCoordinate (H.refine t (H.xO o)) ≡
  refinedCoordinate (H.x10 (H.refine t o))
observedXZ t o = cong refinedCoordinate (H.xz t o)

observedYZ : ∀ t o →
  refinedCoordinate (H.refine t (H.yO o)) ≡
  refinedCoordinate (H.y10 (H.refine t o))
observedYZ t o = cong refinedCoordinate (H.yz t o)

observedEndpoint : ∀ t o →
  refinedCoordinate (Cube.xyz (H.cube t) o) ≡
  refinedCoordinate (Cube.zyx (H.cube t) o)
observedEndpoint t o = cong refinedCoordinate (Cube.xyz-zyx (H.exact t) o)

-- These are forward observations of actual H05 equalities, not a proof
-- that the decoder is injective, or that the one-prefix coefficient
-- formula is equal to the actual decoded observer in the source setoid.
-- That equality uses the signed residue ring transport and inverse
-- digit uniqueness; it must not be replaced by proof-record identity.
