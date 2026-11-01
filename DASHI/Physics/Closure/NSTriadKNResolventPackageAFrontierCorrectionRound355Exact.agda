module DASHI.Physics.Closure.NSTriadKNResolventPackageAFrontierCorrectionRound355Exact where

------------------------------------------------------------------------
-- ROUND355 / BIDI FRONTIER CORRECTION AFTER R342--R354
--
-- R304 was a correct fail-closed snapshot when the nested heat-Schur carrier,
-- finite incidence representation, response majorization, cutoff-uniform
-- signed Gram family, and final R293 -> R240 weld had not yet been built.
--
-- R342--R354 now show that most of that apparent frontier was repository
-- plumbing rather than new analysis.  In particular:
--
--   R342  global nested incidence enumeration,
--   R343  old PairIncidenceData realization,
--   R344  definitional exact finite kernel match,
--   R345  old physical-response majorization bridge,
--   R346  finite row/column Schur certificate constructor,
--   R347  old weighted Schur realization,
--   R348  physical response <= certified Schur budget,
--   R349  genuine two-sided operator-decay adapter for the optional Cotlar lane,
--   R350  old cutoff-uniform Cotlar compiler,
--   R351  spacetime forcing -> old Young-absorption consumer,
--   R352  old Young remainder -> signed Gram flux payment,
--   R353  cutoff-uniform family of signed flux payments -> R293,
--   R354  R293 -> literal R240 physical Package-A budget.
--
-- The corrected authority boundary is therefore:
--
--   physical producers / same-object receipts
--              -> already-owned compilers
--              -> literal R240 Package A.
--
-- This module deliberately does NOT flip the global Package-A or Clay flags.
-- R354 is a conditional constructor: its explicit physical inputs must still
-- be inhabited on the intended NS trajectory.  The point is that there is no
-- longer an additional abstract compiler gap after those inputs are supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNResolventPackageAFrontierRound304Exact as R304
import DASHI.Physics.Closure.NSTriadKNGlobalNestedIncidenceEnumerationRound342Exact as R342
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPairIncidenceRealizationRound343Exact as R343
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedConcreteKernelMatchRound344Exact as R344
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPhysicalResponseMajorizationRound345Exact as R345
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedFiniteSchurCertificateRound346Exact as R346
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedSchurRealizationRound347Exact as R347
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPhysicalSchurBoundRound348Exact as R348
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedOperatorDecayRound349Exact as R349
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedCotlarSteinRound350Exact as R350
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedSpacetimeToResolventRound351Exact as R351
import DASHI.Physics.Closure.NSTriadKNResolventAbsorptionToSignedGramRound352Exact as R352
import DASHI.Physics.Closure.NSTriadKNSignedGramFluxFamilyToR293Round353Exact as R353
import DASHI.Physics.Closure.NSTriadKNR293ToPhysicalPackageARound354Exact as R354

data CorrectedResolventLeaf : Set where
  physicalNestedCoefficient : CorrectedResolventLeaf
  physicalResponseMajorization : CorrectedResolventLeaf
  finiteRowBound : CorrectedResolventLeaf
  finiteColumnBound : CorrectedResolventLeaf
  spacetimeForcingPayment : CorrectedResolventLeaf
  endpointFluxPayments : CorrectedResolventLeaf
  cutoffUniformFluxEnvelope : CorrectedResolventLeaf
  mixedToCompanionPhysicalTransport : CorrectedResolventLeaf
  sameObjectCompanionIntegral : CorrectedResolventLeaf
  optionalTwoSidedCotlarProducts : CorrectedResolventLeaf

data LeafState : Set where suppliedByPhysicalLane conditional optional : LeafState

leafState : CorrectedResolventLeaf → LeafState
leafState physicalNestedCoefficient = suppliedByPhysicalLane
leafState physicalResponseMajorization = suppliedByPhysicalLane
leafState finiteRowBound = suppliedByPhysicalLane
leafState finiteColumnBound = suppliedByPhysicalLane
leafState spacetimeForcingPayment = suppliedByPhysicalLane
leafState endpointFluxPayments = suppliedByPhysicalLane
leafState cutoffUniformFluxEnvelope = suppliedByPhysicalLane
leafState mixedToCompanionPhysicalTransport = suppliedByPhysicalLane
leafState sameObjectCompanionIntegral = suppliedByPhysicalLane
leafState optionalTwoSidedCotlarProducts = optional

oldR304SnapshotDisposition : Admission.RouteDisposition
oldR304SnapshotDisposition = Admission.redirectedReuse

nestedIncidenceCompilerDisposition : Admission.RouteDisposition
nestedIncidenceCompilerDisposition = Admission.redirectedReuse

weightedSchurCompilerDisposition : Admission.RouteDisposition
weightedSchurCompilerDisposition = Admission.redirectedReuse

signedGramConsumerDisposition : Admission.RouteDisposition
signedGramConsumerDisposition = Admission.redirectedReuse

physicalPackageACompilerDisposition : Admission.RouteDisposition
physicalPackageACompilerDisposition = Admission.redirectedReuse

round355R304WasCorrectHistoricalFailClosedSnapshot : Bool
round355R304WasCorrectHistoricalFailClosedSnapshot = true

round355GlobalNestedEnumerationClosed : Bool
round355GlobalNestedEnumerationClosed = R342.round342GlobalNestedPairListClosedByComposition

round355PairIncidenceRealizationClosed : Bool
round355PairIncidenceRealizationClosed = R343.round343PairIncidenceRealizationConstructorClosed

round355ConcreteKernelMatchClosed : Bool
round355ConcreteKernelMatchClosed = R344.round344PointwiseConcreteKernelMatchClosedDefinitionally

round355ResponseMajorizationAdapterClosed : Bool
round355ResponseMajorizationAdapterClosed = R345.round345ResponseMajorizationAdapterClosed

round355PhysicalSchurBoundCompilerClosed : Bool
round355PhysicalSchurBoundCompilerClosed = R348.round348PhysicalFsSchurBoundClosedConditionally

round355R293AdapterClosed : Bool
round355R293AdapterClosed = R353.round353R293AdapterClosed

round355PhysicalPackageAAdapterClosed : Bool
round355PhysicalPackageAAdapterClosed = R354.round354PhysicalPackageAAdapterClosedConditionally

-- The optional TT*/Cotlar path is separate from the positive-kernel Schur path;
-- it requires real two-sided operator-product estimates on one physical family.
round355ScalarSchurMajorantAutomaticallySuppliesCotlarProducts : Bool
round355ScalarSchurMajorantAutomaticallySuppliesCotlarProducts = false

-- Conditional constructor closure is not the same as a global theorem that all
-- intended NS trajectories satisfy the physical premises.
round355GlobalPhysicalPackageATheoremClaimed : Bool
round355GlobalPhysicalPackageATheoremClaimed = false

round355ClayPromotion : Bool
round355ClayPromotion = false

round355PhysicalPackageAAdapterClosedIsTrue :
  round355PhysicalPackageAAdapterClosed ≡ true
round355PhysicalPackageAAdapterClosedIsTrue = refl

round355ScalarSchurMajorantAutomaticallySuppliesCotlarProductsIsFalse :
  round355ScalarSchurMajorantAutomaticallySuppliesCotlarProducts ≡ false
round355ScalarSchurMajorantAutomaticallySuppliesCotlarProductsIsFalse = refl

round355GlobalPhysicalPackageATheoremClaimedIsFalse :
  round355GlobalPhysicalPackageATheoremClaimed ≡ false
round355GlobalPhysicalPackageATheoremClaimedIsFalse = refl

round355ClayPromotionIsFalse : round355ClayPromotion ≡ false
round355ClayPromotionIsFalse = refl
