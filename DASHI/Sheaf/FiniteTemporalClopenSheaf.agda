module DASHI.Sheaf.FiniteTemporalClopenSheaf where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁)

------------------------------------------------------------------------
-- A nontrivial two-chart temporal/clopen site.
--
-- U covers past+overlap, V covers overlap+future.  Local sections carry
-- actual two-valued PNF data and must agree on the shared overlap.

data TimeCell : Set where
  past overlap future : TimeCell

data OpenCell : Set where
  U V UV whole : OpenCell

data PNFValue : Set where
  absent present : PNFValue

record LeftSection : Set where
  constructor leftSection
  field
    pastValue : PNFValue
    overlapValueL : PNFValue

record RightSection : Set where
  constructor rightSection
  field
    overlapValueR : PNFValue
    futureValue : PNFValue

record GlobalSection : Set where
  constructor globalSection
  field
    globalPast : PNFValue
    globalOverlap : PNFValue
    globalFuture : PNFValue

open LeftSection public
open RightSection public
open GlobalSection public

restrictU : GlobalSection → LeftSection
restrictU (globalSection p o f) = leftSection p o

restrictV : GlobalSection → RightSection
restrictV (globalSection p o f) = rightSection o f

restrictUVFromU : LeftSection → PNFValue
restrictUVFromU (leftSection p o) = o

restrictUVFromV : RightSection → PNFValue
restrictUVFromV (rightSection o f) = o

data Compatible : LeftSection → RightSection → Set where
  compatible :
    (p o f : PNFValue) →
    Compatible (leftSection p o) (rightSection o f)

------------------------------------------------------------------------
-- Gluing and uniqueness.

data Glues : GlobalSection → LeftSection → RightSection → Set where
  glued :
    (p o f : PNFValue) →
    Glues
      (globalSection p o f)
      (leftSection p o)
      (rightSection o f)

glue :
  ∀ {l r} →
  Compatible l r →
  Σ GlobalSection (λ g → Glues g l r)
glue (compatible p o f) = globalSection p o f , glued p o f

glueRestrictsU :
  ∀ {l r} →
  (c : Compatible l r) →
  restrictU (proj₁ (glue c)) ≡ l
glueRestrictsU (compatible p o f) = refl

glueRestrictsV :
  ∀ {l r} →
  (c : Compatible l r) →
  restrictV (proj₁ (glue c)) ≡ r
glueRestrictsV (compatible p o f) = refl

glueUnique :
  ∀ {g h l r} →
  Glues g l r →
  Glues h l r →
  g ≡ h
glueUnique (glued p o f) (glued .p .o .f) = refl

------------------------------------------------------------------------
-- A finite overlap metric and a meaningful MereViol interaction.

overlapDistance : PNFValue → PNFValue → Nat
overlapDistance absent absent = zero
overlapDistance present present = zero
overlapDistance absent present = suc zero
overlapDistance present absent = suc zero

compatibleHasZeroOverlapDistance :
  ∀ {l r} →
  Compatible l r →
  overlapDistance (restrictUVFromU l) (restrictUVFromV r) ≡ zero
compatibleHasZeroOverlapDistance (compatible p absent f) = refl
compatibleHasZeroOverlapDistance (compatible p present f) = refl

data MereViol : LeftSection → RightSection → Set where
  absentPresentConflict :
    (p f : PNFValue) →
    MereViol (leftSection p absent) (rightSection present f)
  presentAbsentConflict :
    (p f : PNFValue) →
    MereViol (leftSection p present) (rightSection absent f)

mereViolBlocksGluing :
  ∀ {l r} →
  MereViol l r →
  Compatible l r →
  ⊥
mereViolBlocksGluing (absentPresentConflict p f) ()
mereViolBlocksGluing (presentAbsentConflict p f) ()

------------------------------------------------------------------------
-- Cover and restriction receipts.

record FiniteTemporalCover : Set where
  constructor finiteTemporalCover
  field
    leftOpen rightOpen intersectionOpen unionOpen : OpenCell
    coversPast : Bool
    coversOverlap : Bool
    coversFuture : Bool
    interpretation : String

canonicalFiniteTemporalCover : FiniteTemporalCover
canonicalFiniteTemporalCover =
  finiteTemporalCover U V UV whole true true true
    "U and V form a nontrivial finite temporal cover with one shared clopen overlap"

record FiniteTemporalClopenSheafReceipt : Set where
  constructor mkFiniteTemporalClopenSheafReceipt
  field
    explicitCoverChecked : Bool
    restrictionMapsChecked : Bool
    arbitraryCompatiblePairGlues : Bool
    glueUniqueForEveryCompatiblePair : Bool
    overlapMetricChecked : Bool
    mereViolBlocksIncompatibleOverlap : Bool
    fullArbitraryDASHISitePromoted : Bool
    fullArbitraryDASHISitePromotedIsFalse :
      fullArbitraryDASHISitePromoted ≡ false
    interpretation : String

finiteTemporalClopenSheafReceipt : FiniteTemporalClopenSheafReceipt
finiteTemporalClopenSheafReceipt =
  mkFiniteTemporalClopenSheafReceipt
    true true true true true true false refl
    "a genuine non-singleton two-chart temporal sheaf is checked; promotion to every DASHI temporal or spacetime site still requires the selected covers, restrictions, PNF semantics and metrics"
