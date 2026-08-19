module DASHI.Foundations.BalancedTernaryDependentRecoverableBridgeExact where

------------------------------------------------------------------------
-- SAME-THEOREM-SHAPE BRIDGE
--
-- Instantiate the generic state-dependent recoverable projection core on the
-- exact 27 -> 14 antipodal quotient.  This is the formal bridge between the
-- repo's p-adic/coarse-fine residual intuition and #582's reopening/observer
-- discipline: same mathematics, without identifying the application domains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Core.DependentRecoverableProjectionExact as Dependent
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.BalancedTernaryAntipodalResidualCodecExact as Codec

antipodalReopenExact :
  (triple : Orbit.TritTriple) →
  Codec.decode27
    (Codec.antipodalCode27
      (Codec.coarseClass (Codec.encode27 triple))
      (Codec.orientationResidual (Codec.encode27 triple)))
  ≡ triple
antipodalReopenExact triple =
  trans
    (cong Codec.decode27 (Codec.rebuildCode27 (Codec.encode27 triple)))
    (Codec.decodeAfterEncode27 triple)

canonicalAntipodalDependentProjection :
  Dependent.DependentExactRecoverableProjection
    Orbit.TritTriple Orbit.AntipodalClass27
canonicalAntipodalDependentProjection =
  Dependent.dependentExactRecoverableProjection
    Codec.OrientationResidual27
    (λ triple → Codec.coarseClass (Codec.encode27 triple))
    (λ triple → Codec.orientationResidual (Codec.encode27 triple))
    (λ coarse residual → Codec.decode27 (Codec.antipodalCode27 coarse residual))
    antipodalReopenExact

canonicalProjectionIsOrbitClassifier :
  (triple : Orbit.TritTriple) →
  Dependent.project canonicalAntipodalDependentProjection triple
  ≡ Orbit.classifyAntipodal27 triple
canonicalProjectionIsOrbitClassifier = Codec.coarseOfEncodeIsClassifier

canonicalDependentCodeSeparatesFineCarrier :
  Dependent.DependentCodeSeparating canonicalAntipodalDependentProjection
canonicalDependentCodeSeparatesFineCarrier =
  Dependent.dependentCodeSeparating canonicalAntipodalDependentProjection

canonicalDependentReopeningExact :
  (triple : Orbit.TritTriple) →
  Dependent.decode canonicalAntipodalDependentProjection
    (Dependent.encode canonicalAntipodalDependentProjection triple)
  ≡ triple
canonicalDependentReopeningExact =
  Dependent.decodeEncodeExact canonicalAntipodalDependentProjection
