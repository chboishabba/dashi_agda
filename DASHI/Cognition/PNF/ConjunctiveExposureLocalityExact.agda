{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.ConjunctiveExposureLocalityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_)

------------------------------------------------------------------------
-- Physical sparse-frontier constitution.
--
-- M178/M179 established an important negative result: exact equality of the
-- final candidate/retention relation does not imply sparse intermediate work.
-- A unary posting implementation may expose all partial key matches, then
-- recover conjunction by GROUP BY/counting.  This module therefore separates:
--
--   semantic parity
--   bounded intermediate exposure
--   bounded materialisation
--   bounded rewrite
--
-- Wildcard residuals are explicit.  Missing constraints are not allowed to be
-- reinterpreted as negative evidence merely to obtain a stronger bound.
------------------------------------------------------------------------

-- Four nullable object-candidate axes give exactly sixteen masks.  Constructors
-- are named factor/kind/role/lexical in that bit order.
data CandidateConstraintMask : Set where
  mask0000 mask0001 mask0010 mask0011 : CandidateConstraintMask
  mask0100 mask0101 mask0110 mask0111 : CandidateConstraintMask
  mask1000 mask1001 mask1010 mask1011 : CandidateConstraintMask
  mask1100 mask1101 mask1110 mask1111 : CandidateConstraintMask

candidateMaskCardinality : Nat
candidateMaskCardinality = 16

-- Actor-retention deliberately omits lexical identity, hence eight masks over
-- factor/kind/role.
data RetentionConstraintMask : Set where
  retention000 retention001 retention010 retention011 : RetentionConstraintMask
  retention100 retention101 retention110 retention111 : RetentionConstraintMask

retentionMaskCardinality : Nat
retentionMaskCardinality = 8

record CandidateSignature : Set where
  constructor candidateSignature
  field
    mask : CandidateConstraintMask
    factorKey : Nat
    kindKey : Nat
    roleKey : Nat
    lexicalKey : Nat

open CandidateSignature public

record RetentionSignature : Set where
  constructor retentionSignature
  field
    retentionMask : RetentionConstraintMask
    retentionFactorKey : Nat
    retentionKindKey : Nat
    retentionRoleKey : Nat

open RetentionSignature public

-- Extensional exactness is intentionally independent of execution cost.
record ExtensionalParity : Set₁ where
  field
    FineRow : Set
    legacyRelation : FineRow → Set
    optimizedRelation : FineRow → Set
    relationExact : ∀ row → legacyRelation row ≡ optimizedRelation row

open ExtensionalParity public

-- One observation of the physical realization of an extensionally exact
-- relation.  finalRows is the retained/admitted relation after semantic filters;
-- wildcardResidualRows is unavoidable broad work explicitly charged to demands
-- with no discriminating signature.
record PhysicalWorkObservation : Set where
  constructor physicalWorkObservation
  field
    finalRows : Nat
    wildcardResidualRows : Nat
    intermediateExposureRows : Nat
    materializedRows : Nat
    rewrittenRows : Nat
    semanticallyChangedRows : Nat
    unavoidableRewriteResidualRows : Nat

open PhysicalWorkObservation public

-- The intended runtime contract is E(d) <= c*|A_d| + R_d, generalized here to
-- aggregate observations.  Separate coefficients make it possible for a
-- realization to satisfy exposure locality while still failing materialization
-- or rewrite locality.
record BoundedPhysicalWork
  (observation : PhysicalWorkObservation) : Set where
  constructor boundedPhysicalWork
  field
    exposureConstant : Nat
    materializationConstant : Nat
    rewriteConstant : Nat
    exposureBound :
      intermediateExposureRows observation
        ≤ exposureConstant * finalRows observation
          + wildcardResidualRows observation
    materializationBound :
      materializedRows observation
        ≤ materializationConstant * finalRows observation
          + wildcardResidualRows observation
    rewriteBound :
      rewrittenRows observation
        ≤ rewriteConstant * semanticallyChangedRows observation
          + unavoidableRewriteResidualRows observation

open BoundedPhysicalWork public

-- A sparse implementation certificate is therefore stronger than relation
-- parity.  Semantic equality alone cannot inhabit this record.
record PhysicallySparseExactTransition : Set₁ where
  field
    parity : ExtensionalParity
    observation : PhysicalWorkObservation
    boundedWork : BoundedPhysicalWork observation

open PhysicallySparseExactTransition public

-- Explicit counterexample carrier: two implementations may have exactly the
-- same extensional relation while their exposure counts differ.  This is the
-- formal shape witnessed empirically by the M178/M179 round.
_≢_ : Nat → Nat → Set
m ≢ n = m ≡ n → ⊥

record ExtensionalParityExposureCounterexample : Set₁ where
  field
    parityWitness : ExtensionalParity
    firstExposure : Nat
    secondExposure : Nat
    exposureDiffers : firstExposure ≢ secondExposure

open ExtensionalParityExposureCounterexample public

-- Composite lookup plans choose one exact signature family rather than forming
-- a union of unary postings and reconstructing conjunction after expansion.
record CompositeSignatureLookup : Set₁ where
  field
    Demand : Set
    Profile : Set
    signature : Demand → CandidateSignature
    legacyAdmits : Demand → Profile → Set
    postingAdmits : CandidateSignature → Profile → Set
    postingExact :
      ∀ demand profile →
      legacyAdmits demand profile
        ≡ postingAdmits (signature demand) profile

open CompositeSignatureLookup public
