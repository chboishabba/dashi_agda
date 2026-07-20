module DASHI.Sheaf.TemporalNoodleSheafBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)

import DASHI.Physics.Closure.TemporalSheafProofObligations as Temporal

------------------------------------------------------------------------
-- A deliberately terminal finite inhabitant.
--
-- This checks the shape of the existing DASHI obligation and gives one exact
-- singleton-gluing example.  It is not a full sheaf theorem for arbitrary
-- temporal PNF sections.

data Time2 : Set where
  before after : Time2

data Space2 : Set where
  soilPoint wormPoint : Space2

data Value1 : Set where
  presentValue : Value1

data Section1 : Set where
  strandSection : Section1

data Global1 : Set where
  globalStrand : Global1

validTemporal : Section1 → Time2 → Set
validTemporal strandSection t = ⊤

valueTemporal :
  (s : Section1) →
  (t : Time2) →
  validTemporal s t →
  Value1
valueTemporal strandSection t tt = presentValue

data Overlap1 : Section1 → Section1 → Set where
  overlaps : Overlap1 strandSection strandSection

data Compatible1 : Section1 → Section1 → Set where
  compatible : Compatible1 strandSection strandSection

compatibleSound1 :
  ∀ s₁ s₂ →
  Compatible1 s₁ s₂ →
  ∀ t →
  (p₁ : validTemporal s₁ t) →
  (p₂ : validTemporal s₂ t) →
  valueTemporal s₁ t p₁ ≡ valueTemporal s₂ t p₂
compatibleSound1 strandSection strandSection compatible t tt tt = refl

data MereViol1 : Section1 → Section1 → Set where

mereViolSound1 :
  ∀ s₁ s₂ →
  MereViol1 s₁ s₂ →
  Compatible1 s₁ s₂ →
  ⊥
mereViolSound1 s₁ s₂ () comp

data Glues1 : Global1 → Section1 → Section1 → Set where
  globalGlues : Glues1 globalStrand strandSection strandSection

glue1 :
  ∀ s₁ s₂ →
  Compatible1 s₁ s₂ →
  Σ Global1 (λ g → Glues1 g s₁ s₂)
glue1 strandSection strandSection compatible = globalStrand , globalGlues

data Exclusive1 : Set where
  lineLikeExclusive : Exclusive1

exclusiveSingleValued1 :
  Exclusive1 →
  ∀ s₁ s₂ t →
  (p₁ : validTemporal s₁ t) →
  (p₂ : validTemporal s₂ t) →
  valueTemporal s₁ t p₁ ≡ valueTemporal s₂ t p₂
exclusiveSingleValued1 lineLikeExclusive strandSection strandSection t tt tt = refl

terminalTemporalNoodleSheaf : Temporal.TemporalSheafObligation
terminalTemporalNoodleSheaf =
  record
    { Time = Time2
    ; Section = Section1
    ; Value = Value1
    ; Global = Global1
    ; validAt = validTemporal
    ; valueAt = valueTemporal
    ; overlapRel = Overlap1
    ; compatible = Compatible1
    ; compatibleSound = compatibleSound1
    ; MereViol = MereViol1
    ; mereViolSound = mereViolSound1
    ; Glues = Glues1
    ; glue = glue1
    ; Exclusive = Exclusive1
    ; exclusiveSingleValued = exclusiveSingleValued1
    }

------------------------------------------------------------------------
-- Terminal spacetime extension over the same strand.

validSpacetime : Section1 → Time2 → Space2 → Set
validSpacetime strandSection t x = ⊤

valueSpacetime :
  (s : Section1) →
  (t : Time2) →
  (x : Space2) →
  validSpacetime s t x →
  Value1
valueSpacetime strandSection t x tt = presentValue

spacetimeCompatibleSound1 :
  ∀ s₁ s₂ →
  Compatible1 s₁ s₂ →
  ∀ t x →
  (p₁ : validSpacetime s₁ t x) →
  (p₂ : validSpacetime s₂ t x) →
  valueSpacetime s₁ t x p₁ ≡ valueSpacetime s₂ t x p₂
spacetimeCompatibleSound1 strandSection strandSection compatible t x tt tt = refl

spacetimeMereViolSound1 :
  ∀ s₁ s₂ →
  MereViol1 s₁ s₂ →
  Compatible1 s₁ s₂ →
  ⊥
spacetimeMereViolSound1 s₁ s₂ () comp

exclusiveSpacetimeSingleValued1 :
  Exclusive1 →
  ∀ s₁ s₂ t x →
  (p₁ : validSpacetime s₁ t x) →
  (p₂ : validSpacetime s₂ t x) →
  valueSpacetime s₁ t x p₁ ≡ valueSpacetime s₂ t x p₂
exclusiveSpacetimeSingleValued1 lineLikeExclusive strandSection strandSection t x tt tt = refl

terminalSpacetimeNoodleSheaf : Temporal.SpacetimeSheafObligation
terminalSpacetimeNoodleSheaf =
  record
    { Time = Time2
    ; Space = Space2
    ; Section = Section1
    ; Value = Value1
    ; Global = Global1
    ; _⊑space_ = λ x y → ⊤
    ; spatialOverlap = λ x y → ⊤
    ; validAt = validSpacetime
    ; valueAt = valueSpacetime
    ; overlapRel = Overlap1
    ; compatible = Compatible1
    ; compatibleSound = spacetimeCompatibleSound1
    ; SpacetimeMereViol = MereViol1
    ; spacetimeMereViolSound = spacetimeMereViolSound1
    ; Glues = Glues1
    ; glue = glue1
    ; Exclusive = Exclusive1
    ; exclusiveSpacetimeSingleValued = exclusiveSpacetimeSingleValued1
    }

------------------------------------------------------------------------
-- Foundational QIT sheafification versus DASHI application authority.

record QITSheafificationApplicationBoundary : Set where
  constructor qitSheafificationApplicationBoundary
  field
    qitBaseModule : String
    universalPropertyModule : String
    eliminationModule : String
    quotientInductiveConstructionAvailable : Bool
    leftAdjointUniversalPropertyAvailable : Bool
    propositionEliminationAvailable : Bool
    terminalTemporalInstanceChecked : Bool
    terminalSpacetimeInstanceChecked : Bool
    arbitraryDASHITemporalSheafPromoted : Bool
    arbitraryDASHITemporalSheafPromotedIsFalse :
      arbitraryDASHITemporalSheafPromoted ≡ false
    arbitraryClopenGluingPromoted : Bool
    arbitraryClopenGluingPromotedIsFalse :
      arbitraryClopenGluingPromoted ≡ false
    interpretation : String

canonicalQITSheafificationApplicationBoundary :
  QITSheafificationApplicationBoundary
canonicalQITSheafificationApplicationBoundary =
  qitSheafificationApplicationBoundary
    "Cubical.Categories.Site.Sheafification.Base"
    "Cubical.Categories.Site.Sheafification.UniversalProperty"
    "Cubical.Categories.Site.Sheafification.ElimProp"
    true
    true
    true
    true
    true
    false refl
    false refl
    "the foundational QIT sheafification machinery is distinguished from the still-open restriction, cover, temporal metric, and arbitrary-section gluing obligations in DASHI"

------------------------------------------------------------------------
-- A small explicit non-gluability witness for exclusive temporal claims.

data ExclusiveLocation : Set where
  locationA locationB : ExclusiveLocation

data LocationClaim : Set where
  claimsA claimsB : LocationClaim

claimValue : LocationClaim → ExclusiveLocation
claimValue claimsA = locationA
claimValue claimsB = locationB

data ExclusiveMereViol : LocationClaim → LocationClaim → Set where
  AconflictsB : ExclusiveMereViol claimsA claimsB
  BconflictsA : ExclusiveMereViol claimsB claimsA

data SameLocationClaim : LocationClaim → LocationClaim → Set where
  sameA : SameLocationClaim claimsA claimsA
  sameB : SameLocationClaim claimsB claimsB

exclusiveViolationBlocksCompatibility :
  ∀ c₁ c₂ →
  ExclusiveMereViol c₁ c₂ →
  SameLocationClaim c₁ c₂ →
  ⊥
exclusiveViolationBlocksCompatibility claimsA claimsB AconflictsB ()
exclusiveViolationBlocksCompatibility claimsB claimsA BconflictsA ()
