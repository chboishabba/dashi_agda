module DASHI.Culture.Cuisine.DishIdentityLineageCore where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- A named dish is an identity envelope plus source-bound historical claims.
-- Canon, variant, lineage, popularity, and practical adaptation are distinct.
------------------------------------------------------------------------

data IngredientStatus : Set where
  identityCore allowedAddition contestedAddition canonicallyExcluded : IngredientStatus

record IdentityEnvelope (Ingredient : Set) : Set₁ where
  field
    classify : Ingredient → IngredientStatus
    dishName : String

open IdentityEnvelope public

data VariantKind : Set where
  canonicalRoute regionalVariant diasporaVariant restaurantVariant
  industrialVariant householdAdaptation dietaryAdaptation modernistRecomposition : VariantKind

record DishVariant (Dish Ingredient : Set) : Set₁ where
  field
    baseDish           : Dish
    ingredients        : List Ingredient
    variantKind        : VariantKind
    transformationNote : String

open DishVariant public

data HistoricalClaimKind : Set where
  originClaim precursorClaim earliestTextClaim codificationClaim
  diffusionClaim movementInfluenceClaim ingredientAdoptionClaim : HistoricalClaimKind

data ClaimStanding : Set where
  candidate supported contested promoted blocked : ClaimStanding

data SourceKind : Set where
  cookbookSource archivalMenuSource oralHistorySource scholarlyHistorySource
  practitionerSource regulatorySource commercialSource communitySource : SourceKind

record HistoricalClaim : Set where
  field
    subject       : String
    claimKind     : HistoricalClaimKind
    proposition   : String
    sourceKind    : SourceKind
    sourceLocator : String
    sourceDate    : String
    standing      : ClaimStanding

open HistoricalClaim public

record LineageGraph : Set where
  field
    nodes : List String
    edges : List HistoricalClaim

open LineageGraph public

------------------------------------------------------------------------
-- Classical sauce hierarchy as a typed derivation graph.
------------------------------------------------------------------------

data Sauce : Set where
  bechamel mornay espagnole demiGlace bordelaise : Sauce

data SauceModifier : Set where
  cheeseModifier brownStockReductionModifier wineShallotModifier : SauceModifier

data SauceDerivation : Sauce → Sauce → Set where
  bechamelToMornay       : SauceDerivation bechamel mornay
  espagnoleToDemiGlace  : SauceDerivation espagnole demiGlace
  demiGlaceToBordelaise : SauceDerivation demiGlace bordelaise

data SaucePath : Sauce → Sauce → Set where
  pathStop : {s : Sauce} → SaucePath s s
  pathStep : {a b c : Sauce} → SauceDerivation a b → SaucePath b c → SaucePath a c

mornayDerivesFromBechamel : SaucePath bechamel mornay
mornayDerivesFromBechamel = pathStep bechamelToMornay pathStop

bordelaiseDerivesFromEspagnole : SaucePath espagnole bordelaise
bordelaiseDerivesFromEspagnole =
  pathStep espagnoleToDemiGlace
    (pathStep demiGlaceToBordelaise pathStop)

------------------------------------------------------------------------
-- Carbonara is included as a finite identity-envelope example only.
-- Historical and regional authority remain source-gated elsewhere.
------------------------------------------------------------------------

data CarbonaraIngredient : Set where
  pasta egg pecorino guanciale blackPepper cream pancetta smokedBacon : CarbonaraIngredient

carbonaraIngredientStatus : CarbonaraIngredient → IngredientStatus
carbonaraIngredientStatus pasta       = identityCore
carbonaraIngredientStatus egg         = identityCore
carbonaraIngredientStatus pecorino    = identityCore
carbonaraIngredientStatus guanciale   = identityCore
carbonaraIngredientStatus blackPepper = identityCore
carbonaraIngredientStatus cream       = canonicallyExcluded
carbonaraIngredientStatus pancetta    = contestedAddition
carbonaraIngredientStatus smokedBacon = contestedAddition

carbonaraCandidateEnvelope : IdentityEnvelope CarbonaraIngredient
carbonaraCandidateEnvelope = record
  { classify = carbonaraIngredientStatus
  ; dishName = "carbonara"
  }

creamIsOutsideCandidateCanon :
  classify carbonaraCandidateEnvelope cream ≡ canonicallyExcluded
creamIsOutsideCandidateCanon = refl
