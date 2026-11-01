{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalB4PhysicalR440AnalyticInterfaceExact where

------------------------------------------------------------------------
-- CANONICAL NAVIER--STOKES B4 PHYSICAL R440 ANALYTIC INTERFACE
--
-- DASHI extension.  The existing non-Round B frontier has already reduced the
-- B4 representation problem to one literal physical signed R440 payment:
--
--   signedWork ≤ thetaD * coreMass + cD * localED
--   0 ≤ thetaD
--   half + thetaD < one
--
-- This module owns only that analytic socket.  Every source object, scalar,
-- arithmetic operation, order relation and same-source attachment is fixed
-- externally.  The record can carry evidence for the fixed inequalities but
-- cannot choose the objects or predicates it is asked to prove.
--
-- The bridge to the earlier canonical B4 owner is deliberately explicit: an
-- external implication is required to identify this exact analytic package
-- with the legacy source-facing payment predicate.  No same-object meaning is
-- manufactured here.
------------------------------------------------------------------------

open import DASHI.Physics.Closure.NSCanonicalB4PhysicalR440PaymentResidualExact as B4 using ()

record CanonicalB4PhysicalR440AnalyticPayment
    (SelectedPeriodicSource Scalar : Set)
    (selectedSource : SelectedPeriodicSource)
    (signedWork coreMass localED thetaD cD zero half one : Scalar)
    (_+_ _*_ : Scalar → Scalar → Scalar)
    (_≤_ _<_ : Scalar → Scalar → Set)
    (SignedWorkBelongsToSource : SelectedPeriodicSource → Scalar → Set)
    (CoreMassBelongsToSource : SelectedPeriodicSource → Scalar → Set)
    (LocalEDBelongsToSource : SelectedPeriodicSource → Scalar → Set)
    (signedWorkSourceAttachment :
      SignedWorkBelongsToSource selectedSource signedWork)
    (coreMassSourceAttachment :
      CoreMassBelongsToSource selectedSource coreMass)
    (localEDSourceAttachment :
      LocalEDBelongsToSource selectedSource localED) : Set₁ where
  field
    signedPhysicalR440Payment :
      signedWork ≤ ((thetaD * coreMass) + (cD * localED))

    thetaDNonnegative :
      zero ≤ thetaD

    strictHalfMargin :
      (half + thetaD) < one

------------------------------------------------------------------------
-- Compatibility bridge into the already-canonical opaque B4 owner.
------------------------------------------------------------------------

canonicalB4PaymentResidualFromAnalytic :
  ∀ {SelectedPeriodicSource Scalar : Set}
    (selectedSource : SelectedPeriodicSource)
    (signedWork coreMass localED thetaD cD zero half one : Scalar)
    (_+_ _*_ : Scalar → Scalar → Scalar)
    (_≤_ _<_ : Scalar → Scalar → Set)
    (SignedWorkBelongsToSource : SelectedPeriodicSource → Scalar → Set)
    (CoreMassBelongsToSource : SelectedPeriodicSource → Scalar → Set)
    (LocalEDBelongsToSource : SelectedPeriodicSource → Scalar → Set)
    (signedWorkSourceAttachment :
      SignedWorkBelongsToSource selectedSource signedWork)
    (coreMassSourceAttachment :
      CoreMassBelongsToSource selectedSource coreMass)
    (localEDSourceAttachment :
      LocalEDBelongsToSource selectedSource localED)
    (PhysicalR440NoncoreCorePayment : SelectedPeriodicSource → Set)
    (analyticPaymentImpliesCanonicalPayment :
      CanonicalB4PhysicalR440AnalyticPayment
        SelectedPeriodicSource Scalar selectedSource
        signedWork coreMass localED thetaD cD zero half one
        _+_ _*_ _≤_ _<_
        SignedWorkBelongsToSource
        CoreMassBelongsToSource
        LocalEDBelongsToSource
        signedWorkSourceAttachment
        coreMassSourceAttachment
        localEDSourceAttachment
      → PhysicalR440NoncoreCorePayment selectedSource)
    → CanonicalB4PhysicalR440AnalyticPayment
        SelectedPeriodicSource Scalar selectedSource
        signedWork coreMass localED thetaD cD zero half one
        _+_ _*_ _≤_ _<_
        SignedWorkBelongsToSource
        CoreMassBelongsToSource
        LocalEDBelongsToSource
        signedWorkSourceAttachment
        coreMassSourceAttachment
        localEDSourceAttachment
    → B4.CanonicalB4PhysicalR440PaymentResidual
        SelectedPeriodicSource selectedSource
        PhysicalR440NoncoreCorePayment
canonicalB4PaymentResidualFromAnalytic
  selectedSource
  signedWork coreMass localED thetaD cD zero half one
  _+_ _*_ _≤_ _<_
  SignedWorkBelongsToSource
  CoreMassBelongsToSource
  LocalEDBelongsToSource
  signedWorkSourceAttachment
  coreMassSourceAttachment
  localEDSourceAttachment
  PhysicalR440NoncoreCorePayment
  analyticPaymentImpliesCanonicalPayment
  analyticPayment =
    record
      { physicalR440NoncoreCorePayment =
          analyticPaymentImpliesCanonicalPayment analyticPayment
      }
