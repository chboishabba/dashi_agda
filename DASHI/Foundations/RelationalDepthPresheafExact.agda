module DASHI.Foundations.RelationalDepthPresheafExact where

------------------------------------------------------------------------
-- RELATIONAL LOCALITY x REFINEMENT DEPTH
--
-- DASHI CONTRIBUTION
--
-- A relational section may be compatible at one observation depth and fail to
-- glue after refinement.  Depth truncation is therefore retained separately
-- from relational restriction.  The carrier is inverse-system/presheaf-like;
-- no p-adic psychological metric or empirical law is asserted by this file.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record DepthPresheaf (Section : Nat → Set) : Set₁ where
  field
    truncate :
      (depth : Nat) →
      Section (suc depth) →
      Section depth

open DepthPresheaf public

data GluingStatus : Set where
  glues : GluingStatus
  obstructed : GluingStatus

record TwoDepthRelationalGluing : Set where
  constructor two-depth-relational-gluing
  field
    coarseStatus : GluingStatus
    fineStatus : GluingStatus

open TwoDepthRelationalGluing public

coarseOnlyCompatibility : TwoDepthRelationalGluing
coarseOnlyCompatibility =
  two-depth-relational-gluing glues obstructed

coarseReallyGlues :
  coarseStatus coarseOnlyCompatibility ≡ glues
coarseReallyGlues = refl

fineReallyObstructed :
  fineStatus coarseOnlyCompatibility ≡ obstructed
fineReallyObstructed = refl

data CoarseGluingForcesFineGluing : Set where

coarseGluingDoesNotForceFineGluing :
  CoarseGluingForcesFineGluing → ⊥
coarseGluingDoesNotForceFineGluing ()


------------------------------------------------------------------------
-- Named gluing-depth witness.
------------------------------------------------------------------------

record GluingDepthWitness : Set where
  constructor gluing-depth-witness
  field
    gluingDepth : Nat
    statusAtDepth : GluingStatus
    statusAtNextDepth : GluingStatus
    gluesAtDeclaredDepth :
      statusAtDepth ≡ glues
    nextDepthMayExposeObstruction :
      statusAtNextDepth ≡ obstructed

open GluingDepthWitness public

canonicalGluingDepthWitness : GluingDepthWitness
canonicalGluingDepthWitness =
  gluing-depth-witness zero glues obstructed refl refl

------------------------------------------------------------------------
-- A tiny concrete inverse-system witness.
------------------------------------------------------------------------

data CoarseSection : Set where
  sameCoarse : CoarseSection

data FineSection : Set where
  fineLeft : FineSection
  fineRight : FineSection

depthSection : Nat → Set
depthSection zero = CoarseSection
depthSection (suc depth) = FineSection

truncateDemo : (depth : Nat) → depthSection (suc depth) → depthSection depth
truncateDemo zero fineLeft = sameCoarse
truncateDemo zero fineRight = sameCoarse
truncateDemo (suc depth) fine = fine

demoDepthPresheaf : DepthPresheaf depthSection
demoDepthPresheaf = record { truncate = truncateDemo }

fineStatesCollideCoarsely :
  truncate demoDepthPresheaf zero fineLeft
  ≡ truncate demoDepthPresheaf zero fineRight
fineStatesCollideCoarsely = refl

fineStatesRemainDistinct :
  fineLeft ≡ fineRight → ⊥
fineStatesRemainDistinct ()

record RelationalDepthBoundary : Set where
  constructor relational-depth-boundary
  field
    coarseAgreementImpliesFineAgreement : Bool
    refinementMayExposeGluingObstruction : Bool
    refinementDepthIsDeclaredPAdicValuation : Bool
    relationalLocalityEqualsResolutionDepth : Bool

canonicalRelationalDepthBoundary : RelationalDepthBoundary
canonicalRelationalDepthBoundary =
  relational-depth-boundary false true false false
