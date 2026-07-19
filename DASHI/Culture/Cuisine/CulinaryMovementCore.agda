module DASHI.Culture.Cuisine.CulinaryMovementCore where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Culinary movements are transformation regimes, not dish identities.
------------------------------------------------------------------------

data MovementValue : Set where
  precision              : MovementValue
  regionality            : MovementValue
  biodiversity           : MovementValue
  restraint              : MovementValue
  novelty                : MovementValue
  hospitality            : MovementValue
  antiIndustrialPractice : MovementValue
  scientificExplanation  : MovementValue
  seasonality            : MovementValue
  luxury                 : MovementValue
  reproducibility        : MovementValue
  craftTransmission      : MovementValue

data TechniqueFamily : Set where
  classicalReduction         : TechniqueFamily
  fermentation              : TechniqueFamily
  liveFire                  : TechniqueFamily
  lowTemperatureCooking     : TechniqueFamily
  hydrocolloidTransformation : TechniqueFamily
  spherification            : TechniqueFamily
  foaming                   : TechniqueFamily
  deconstruction            : TechniqueFamily
  preservation              : TechniqueFamily
  noseToTail                : TechniqueFamily
  wholePlant                : TechniqueFamily

data AestheticPriority : Set where
  clarity       : AestheticPriority
  abundance     : AestheticPriority
  minimalism    : AestheticPriority
  surprise      : AestheticPriority
  naturalism    : AestheticPriority
  theatricality : AestheticPriority
  rusticity     : AestheticPriority
  refinement    : AestheticPriority
  contrast      : AestheticPriority
  continuity    : AestheticPriority

record MovementRegime : Set where
  field
    movementName    : String
    values          : List MovementValue
    techniques      : List TechniqueFamily
    aesthetics      : List AestheticPriority
    historicalNote  : String
    authoritySource : String

open MovementRegime public

data MovementProjectionKind : Set where
  aligned            : MovementProjectionKind
  influencedBy       : MovementProjectionKind
  criticalResponse   : MovementProjectionKind
  hybridizedWith     : MovementProjectionKind
  externallyLabelled : MovementProjectionKind

record DishMovementProjection : Set where
  field
    dishName       : String
    movement       : MovementRegime
    projectionKind : MovementProjectionKind
    transformation : String
    sourceLocator  : String

open DishMovementProjection public

data MovementIdentityBoundary : Set where
  movementProjectionDoesNotFixDishIdentity        : MovementIdentityBoundary
  sharedTechniqueDoesNotFixMovement               : MovementIdentityBoundary
  movementLabelDoesNotPromoteHistoricalAuthority  : MovementIdentityBoundary

modernistCandidateRegime : MovementRegime
modernistCandidateRegime = record
  { movementName = "modernist cuisine candidate regime"
  ; values = precision ∷ novelty ∷ scientificExplanation ∷ reproducibility ∷ []
  ; techniques = lowTemperatureCooking ∷ hydrocolloidTransformation ∷
                 spherification ∷ foaming ∷ deconstruction ∷ []
  ; aesthetics = surprise ∷ clarity ∷ theatricality ∷ []
  ; historicalNote = "source-bound historical description required"
  ; authoritySource = "unpromoted until receipt supplied"
  }

slowFoodCandidateRegime : MovementRegime
slowFoodCandidateRegime = record
  { movementName = "slow-food candidate regime"
  ; values = regionality ∷ biodiversity ∷ antiIndustrialPractice ∷
             seasonality ∷ craftTransmission ∷ []
  ; techniques = fermentation ∷ preservation ∷ wholePlant ∷ []
  ; aesthetics = naturalism ∷ rusticity ∷ continuity ∷ []
  ; historicalNote = "source-bound historical description required"
  ; authoritySource = "unpromoted until receipt supplied"
  }
