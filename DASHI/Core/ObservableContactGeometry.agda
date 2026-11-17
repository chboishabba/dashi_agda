module DASHI.Core.ObservableContactGeometry where

open import Agda.Builtin.Bool using (Bool)

import DASHI.Core.ComparisonLawCore as Comparison
import DASHI.Core.FibreRestrictionCore as Restriction

------------------------------------------------------------------------
-- Generic projected-contact geometry.
--
-- A contact surface is not primitive here.  The primitive is governed
-- interconnection:
--
-- carrier projection
-- -> comparison on a shared surface
-- -> residual on failed agreement
-- -> fibre restriction without hidden-carrier recovery
--
-- Observable contact is then the case where one side of the comparison is a
-- trace/measurement-facing surface.
------------------------------------------------------------------------

record ObservableContactGeometry : Set₁ where
  constructor observableContactGeometry
  field
    Carrier                : Set
    Observable             : Set
    Trace                  : Set
    FibreEvidence          : Set
    Projection             : Carrier → Observable
    Fibre                  : Observable → Set
    TraceProjection        : Trace → Observable
    Residual               : Observable → Observable → Set
    ComparisonLaw          : Observable → Observable → Set
    FibreRestriction       : FibreEvidence → Observable → Set
    doesNotRecoverCarrier  : Bool
    fibreRestrictionPromotesTruth : Bool
    Transition             : Trace → Trace → Set
    ContactReceipt         : Set

open ObservableContactGeometry public

comparisonCore :
  (geometry : ObservableContactGeometry) →
  Comparison.ComparisonLawCore
comparisonCore geometry =
  Comparison.comparisonLawCore
    (Carrier geometry)
    (Trace geometry)
    (Observable geometry)
    (Projection geometry)
    (TraceProjection geometry)
    (Residual geometry)
    (ComparisonLaw geometry)

fibreRestrictionCore :
  (geometry : ObservableContactGeometry) →
  Restriction.FibreRestrictionCore
fibreRestrictionCore geometry =
  Restriction.fibreRestrictionCore
    (Carrier geometry)
    (Observable geometry)
    (FibreEvidence geometry)
    (Projection geometry)
    (Fibre geometry)
    (FibreRestriction geometry)
    (doesNotRecoverCarrier geometry)
    (fibreRestrictionPromotesTruth geometry)

ProjectionLossWitness :
  (geometry : ObservableContactGeometry) →
  Observable geometry → Set
ProjectionLossWitness geometry =
  Restriction.ProjectionLossWitness (fibreRestrictionCore geometry)

ProjectedResidual :
  (geometry : ObservableContactGeometry) →
  Observable geometry → Observable geometry → Set
ProjectedResidual geometry =
  Comparison.ComparisonResidual (comparisonCore geometry)

FibreRestrictionEvidence :
  (geometry : ObservableContactGeometry) →
  Restriction.Evidence (fibreRestrictionCore geometry) →
  Observable geometry → Set
FibreRestrictionEvidence geometry =
  Restriction.restrictsFibre (fibreRestrictionCore geometry)
