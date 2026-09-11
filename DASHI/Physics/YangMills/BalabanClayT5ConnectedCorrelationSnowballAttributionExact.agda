{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5ConnectedCorrelationSnowballAttributionExact where

------------------------------------------------------------------------
-- CONNECTED-CORRELATION SNOWBALL ATTRIBUTION / NON-PROMOTING SOURCE MAP
--
-- Purpose: retain primary-source, DOI, QID, Dewey and OEIS coordinates while
-- keeping them strictly separate from theorem payment.  The live Step-V
-- producer remains the same-carrier two-marked connected-cluster tail in
-- `BalabanClayT5TwoMarkedConnectedClusterTailExact`.
--
-- Primary sources / donor roles:
--
-- * Tadeusz Balaban,
--   "Renormalization Group Approach to Lattice Gauge Field Theories. II.
--    Cluster Expansions", CMP 116 (1988), 1--22.
--   DOI: 10.1007/BF01239022.
--   Role: primary gauge-theory cluster-expansion architecture.
--
-- * Roman Kotecky and David Preiss,
--   "Cluster Expansion for Abstract Polymer Models", CMP 103 (1986), 491--498.
--   DOI: 10.1007/BF01211762.
--   Role: primary abstract polymer convergence theorem.
--
-- * Roberto Fernandez and Aldo Procacci,
--   "Cluster Expansion for Abstract Polymer Models. New Bounds from an Old
--    Approach", CMP 274 (2007), 123--140.
--   DOI: 10.1007/s00220-007-0279-2; arXiv: math-ph/0605041.
--   Role: stronger abstract convergence/tree-graph producer family.
--
-- * Rodrigo Bissacot, Roberto Fernandez and Aldo Procacci,
--   "On the Convergence of Cluster Expansions for Polymer Gases",
--   J. Stat. Phys. 139 (2010), 598--617.
--   DOI: 10.1007/s10955-010-9956-1; arXiv: 1002.3261.
--   Role: abstract-polymer correlation-bound donor.
--
-- * Oliver Penrose and Joel L. Lebowitz,
--   "On the Exponential Decay of Correlation Functions", CMP 39 (1974),
--   165--184. DOI: 10.1007/BF01614239.
--   Role: independent correlation-decay / transfer-matrix donor.
--
-- * Konrad Osterwalder and Robert Schrader,
--   "Axioms for Euclidean Green's Functions II", CMP 42 (1975), 281--305.
--   DOI: 10.1007/BF01608978.
--   Role: downstream Euclidean/OS reconstruction authority.
--
-- QID / Dewey / OEIS are discovery coordinates only.  A DOI/QID/classification
-- match does not prove carrier identity, applicability, or the YM estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.BalabanMarkedLogPartitionConnectedCorrelationCompilerExact as Marked

record ConnectedCorrelationSnowballAttribution : Set where
  constructor connected-correlation-snowball-attribution
  field
    balabanClusterII_DOI : String
    koteckyPreiss_DOI : String
    fernandezProcacci_DOI : String
    bissacotFernandezProcacci_DOI : String
    penroseLebowitz_DOI : String
    osterwalderSchraderII_DOI : String

    romanKoteckyQID : String
    balabanClusterIIPaperQID : String
    koteckyPreissPaperQID : String
    connectedCorrelationConceptQID : String

    deweyCoordinate : String
    oeisCoordinate : String

    balabanIIPrimaryGaugeClusterSource : Bool
    balabanIIPrimaryGaugeClusterSourceIsTrue :
      balabanIIPrimaryGaugeClusterSource ≡ true

    kpPrimaryAbstractPolymerSource : Bool
    kpPrimaryAbstractPolymerSourceIsTrue :
      kpPrimaryAbstractPolymerSource ≡ true

    citationsAlonePayFourDimensionalYMClustering : Bool
    citationsAlonePayFourDimensionalYMClusteringIsFalse :
      citationsAlonePayFourDimensionalYMClustering ≡ false

    qidOrDeweyOrOEISCreatesTheoremAuthority : Bool
    qidOrDeweyOrOEISCreatesTheoremAuthorityIsFalse :
      qidOrDeweyOrOEISCreatesTheoremAuthority ≡ false

    clusterWeightDecayAlonePaysSameCarrierTwoSourceDecay : Bool
    clusterWeightDecayAlonePaysSameCarrierTwoSourceDecayIsFalse :
      clusterWeightDecayAlonePaysSameCarrierTwoSourceDecay ≡ false

    twoMarkedConnectingTailIsCurrentStepVPayment : Bool
    twoMarkedConnectingTailIsCurrentStepVPaymentIsTrue :
      twoMarkedConnectingTailIsCurrentStepVPayment ≡ true

open ConnectedCorrelationSnowballAttribution public

canonicalConnectedCorrelationSnowballAttribution :
  ConnectedCorrelationSnowballAttribution
canonicalConnectedCorrelationSnowballAttribution =
  connected-correlation-snowball-attribution
    "10.1007/BF01239022"
    "10.1007/BF01211762"
    "10.1007/s00220-007-0279-2"
    "10.1007/s10955-010-9956-1"
    "10.1007/BF01614239"
    "10.1007/BF01608978"
    "Q57054683"
    "unresolved"
    "unresolved"
    "unresolved"
    "530.15"
    "not-applicable"
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl

-- Re-export the exact compiler consequence so the attribution owner points to
-- theorem content without duplicating or promoting it.
connectedTailCompiler = TwoMark.connectedResponseHasConfiguredSeparationTail

markedSourceConnectedCorrelationCompiler =
  Marked.connectedCorrelationDecayFromMarkedSource

sourceMetadataProvesNothingByItself : Bool
sourceMetadataProvesNothingByItself = false

sourceMetadataProvesNothingByItselfIsFalse :
  sourceMetadataProvesNothingByItself ≡ false
sourceMetadataProvesNothingByItselfIsFalse = refl
