module DASHI.Core.PlumwoodMasterModelOperationFamilyExact where

------------------------------------------------------------------------
-- PLUMWOOD MASTER-MODEL OPERATION FAMILY
--
-- SOURCE CALIBRATION
-- Val Plumwood, Feminism and the Mastery of Nature, Routledge, 1993.
-- ISBN 9780415068109. No DOI asserted for the monograph.
--
-- Plumwood motivates distinct operations including backgrounding, radical
-- exclusion/hyperseparation, incorporation, instrumentalism and homogenisation.
-- DASHI keeps them separately typed and does not attribute the synthetic
-- independence countermodels below to Plumwood.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record MasterModelOperations (Dominant Subordinated : Set) : Set₁ where
  constructor master-model-operations
  field
    Backgrounds : Dominant → Subordinated → Set
    Hyperseparates : Dominant → Subordinated → Set
    Incorporates : Dominant → Subordinated → Set
    Instrumentalises : Dominant → Subordinated → Set
    Homogenises : Dominant → Subordinated → Set

open MasterModelOperations public

data D : Set where d0 d1 : D
data S : Set where s0 s1 : S

data Backgrounding : D → S → Set where bg : Backgrounding d0 s0
data Hyperseparation : D → S → Set where hs : Hyperseparation d1 s0
data Incorporation : D → S → Set where inc : Incorporation d0 s1
data Instrumentalism : D → S → Set where inst : Instrumentalism d1 s1
data Homogenisation : D → S → Set where hom : Homogenisation d0 s0

canonicalOperations : MasterModelOperations D S
canonicalOperations =
  master-model-operations Backgrounding Hyperseparation Incorporation Instrumentalism Homogenisation

backgroundingDoesNotAutoGiveHyperseparation :
  Backgrounding d0 s0 → Hyperseparation d0 s0 → ⊥
backgroundingDoesNotAutoGiveHyperseparation bg ()

incorporationDoesNotAutoGiveHomogenisation :
  Incorporation d0 s1 → Homogenisation d0 s1 → ⊥
incorporationDoesNotAutoGiveHomogenisation inc ()

instrumentalismDoesNotAutoGiveBackgrounding :
  Instrumentalism d1 s1 → Backgrounding d1 s1 → ⊥
instrumentalismDoesNotAutoGiveBackgrounding inst ()

record MasterModelOperationBoundary : Set where
  constructor master-model-operation-boundary
  field
    hierarchyIsOneUndifferentiatedBool : Bool
    hierarchyIsOneUndifferentiatedBoolIsFalse :
      hierarchyIsOneUndifferentiatedBool ≡ false
    plumwoodProvedTheseFiniteCountermodels : Bool
    plumwoodProvedTheseFiniteCountermodelsIsFalse :
      plumwoodProvedTheseFiniteCountermodels ≡ false
    presenceOfOneOperationImpliesAllOthers : Bool
    presenceOfOneOperationImpliesAllOthersIsFalse :
      presenceOfOneOperationImpliesAllOthers ≡ false

canonicalMasterModelOperationBoundary : MasterModelOperationBoundary
canonicalMasterModelOperationBoundary =
  master-model-operation-boundary false refl false refl false refl
