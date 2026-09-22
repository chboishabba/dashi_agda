module DASHI.Law.SensibLawYindjibarndiAffectedConsumerRecomputeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawYindjibarndiEmpiricalAuthorityJoinExact as Y

------------------------------------------------------------------------
-- S19.10 EXACT AFFECTED-CONSUMER RECOMPUTATION
--
-- A changed shared coordinate reopens exactly the consumers whose reviewed
-- dependency slices contain that coordinate.  Citation, conceptual adjacency,
-- and membership in the same legal programme are not fanout proofs.
------------------------------------------------------------------------

data Consumer : Set where
  yindjibarndi : Consumer
  sharedNativeTitleAuthorities : Consumer
  maboAcquisition : Consumer
  pabaiControl : Consumer
  munkaraControl : Consumer

data ChangedCoordinate : Set where
  yunupinguAcquisition : ChangedCoordinate
  maboAcquisitionDistinction : ChangedCoordinate

DependsOn : Consumer → ChangedCoordinate → Set
DependsOn yindjibarndi yunupinguAcquisition = ⊤
DependsOn yindjibarndi maboAcquisitionDistinction = ⊤
DependsOn sharedNativeTitleAuthorities yunupinguAcquisition = ⊤
DependsOn sharedNativeTitleAuthorities maboAcquisitionDistinction = ⊥
DependsOn maboAcquisition yunupinguAcquisition = ⊥
DependsOn maboAcquisition maboAcquisitionDistinction = ⊤
DependsOn pabaiControl yunupinguAcquisition = ⊥
DependsOn pabaiControl maboAcquisitionDistinction = ⊥
DependsOn munkaraControl yunupinguAcquisition = ⊥
DependsOn munkaraControl maboAcquisitionDistinction = ⊥

data Recompute : Consumer → ChangedCoordinate → Set where
  becauseExactDependency :
    ∀ {consumer coordinate} →
    DependsOn consumer coordinate →
    Recompute consumer coordinate

yindjibarndiRecomputesForYunupingu :
  Recompute yindjibarndi yunupinguAcquisition
yindjibarndiRecomputesForYunupingu =
  becauseExactDependency tt

sharedAuthorityRecomputesForYunupingu :
  Recompute sharedNativeTitleAuthorities yunupinguAcquisition
sharedAuthorityRecomputesForYunupingu =
  becauseExactDependency tt

yindjibarndiRecomputesForMabo :
  Recompute yindjibarndi maboAcquisitionDistinction
yindjibarndiRecomputesForMabo =
  becauseExactDependency tt

maboConsumerRecomputesForMabo :
  Recompute maboAcquisition maboAcquisitionDistinction
maboConsumerRecomputesForMabo =
  becauseExactDependency tt

------------------------------------------------------------------------
-- Controls cannot be reopened without manufacturing a dependency witness.
------------------------------------------------------------------------

pabaiDoesNotRecomputeForYunupingu :
  Recompute pabaiControl yunupinguAcquisition → ⊥
pabaiDoesNotRecomputeForYunupingu
  (becauseExactDependency ())

pabaiDoesNotRecomputeForMabo :
  Recompute pabaiControl maboAcquisitionDistinction → ⊥
pabaiDoesNotRecomputeForMabo
  (becauseExactDependency ())

munkaraDoesNotRecomputeForYunupingu :
  Recompute munkaraControl yunupinguAcquisition → ⊥
munkaraDoesNotRecomputeForYunupingu
  (becauseExactDependency ())

munkaraDoesNotRecomputeForMabo :
  Recompute munkaraControl maboAcquisitionDistinction → ⊥
munkaraDoesNotRecomputeForMabo
  (becauseExactDependency ())

------------------------------------------------------------------------
-- The empirical coordinate owners remain exactly those already reviewed in
-- the Yindjibarndi dependency slice.
------------------------------------------------------------------------

yunupinguCoordinateRef : String
yunupinguCoordinateRef =
  Y.SharedCoordinate.coordinateRef Y.yunupinguAcquisitionCoordinate

maboCoordinateRef : String
maboCoordinateRef =
  Y.SharedCoordinate.coordinateRef Y.maboAcquisitionDistinctionCoordinate

data AdjacencyCreatesAffectedConsumer : Set where
data UnreviewedJoinCreatesAffectedConsumer : Set where
data RecomputeCreatesClaimTruth : Set where

adjacencyCannotCreateFanout :
  AdjacencyCreatesAffectedConsumer → ⊥
adjacencyCannotCreateFanout ()

unreviewedJoinCannotCreateFanout :
  UnreviewedJoinCreatesAffectedConsumer → ⊥
unreviewedJoinCannotCreateFanout ()

recomputeDoesNotCreateTruth :
  RecomputeCreatesClaimTruth → ⊥
recomputeDoesNotCreateTruth ()

record YindjibarndiAffectedConsumerBoundary : Set where
  constructor yindjibarndiAffectedConsumerBoundary
  field
    yunupinguDeltaReopensYindjibarndi : Bool
    yunupinguDeltaReopensYindjibarndiIsTrue :
      yunupinguDeltaReopensYindjibarndi ≡ true

    yunupinguDeltaReopensSharedAuthorityConsumer : Bool
    yunupinguDeltaReopensSharedAuthorityConsumerIsTrue :
      yunupinguDeltaReopensSharedAuthorityConsumer ≡ true

    maboDeltaReopensYindjibarndi : Bool
    maboDeltaReopensYindjibarndiIsTrue :
      maboDeltaReopensYindjibarndi ≡ true

    maboDeltaReopensMaboSpecificConsumer : Bool
    maboDeltaReopensMaboSpecificConsumerIsTrue :
      maboDeltaReopensMaboSpecificConsumer ≡ true

    pabaiReopensByAdjacency : Bool
    pabaiReopensByAdjacencyIsFalse :
      pabaiReopensByAdjacency ≡ false

    munkaraReopensByAdjacency : Bool
    munkaraReopensByAdjacencyIsFalse :
      munkaraReopensByAdjacency ≡ false

    recomputeCreatesClaimTruth : Bool
    recomputeCreatesClaimTruthIsFalse :
      recomputeCreatesClaimTruth ≡ false

open YindjibarndiAffectedConsumerBoundary public

canonicalYindjibarndiAffectedConsumerBoundary :
  YindjibarndiAffectedConsumerBoundary
canonicalYindjibarndiAffectedConsumerBoundary =
  yindjibarndiAffectedConsumerBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
