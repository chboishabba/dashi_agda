module DASHI.Biology.Protein.ProteinFunctionProjection where

-- Protein function is projected from sequence, conformation, environment,
-- interaction partners, modification, localisation, and history.  Sequence or
-- fold alone is not promoted to a complete function theorem.
record ProteinFunctionSystem : Set₁ where
  field
    Sequence      : Set
    Conformation  : Set
    Environment   : Set
    Partner       : Set
    Modification  : Set
    Localisation  : Set
    History       : Set
    Function      : Set

    functionAt :
      Sequence → Conformation → Environment → Partner →
      Modification → Localisation → History → Function

    PhysicallyRealised : Function → Set
    ExperimentallyValidated : Function → Set

record ProteinFunctionWitness
  (P : ProteinFunctionSystem) : Set₁ where
  open ProteinFunctionSystem P
  field
    sequence     : Sequence
    conformation : Conformation
    environment  : Environment
    partner      : Partner
    modification : Modification
    localisation : Localisation
    history      : History

    realised :
      PhysicallyRealised
        (functionAt sequence conformation environment partner
          modification localisation history)

-- Shared representation plus task-specific heads, matching the disciplined
-- interpretation of multi-property protein predictors: a latent carrier can be
-- shared without identifying predicted outputs with proved biological facts.
record SharedProteinRepresentation : Set₁ where
  field
    Sequence       : Set
    Representation : Set
    Task           : Set
    Output         : Set

    encode : Sequence → Representation
    head   : Task → Representation → Output

record ProteinPredictionAuthorityBoundary
  (R : SharedProteinRepresentation) : Set₁ where
  open SharedProteinRepresentation R
  field
    PredictionContext : Set
    GroundTruth       : Set

    predicts : PredictionContext → Task → Sequence → Output
    validatesAgainst : Output → GroundTruth → Set

    representationIsNotMechanismByDefinition : Set
    predictionIsNotExperimentalAuthority     : Set
    taskHeadIsNotUniversalFunctionProjection : Set

record ContextDependentFunctionWitness
  (P : ProteinFunctionSystem) : Set₁ where
  open ProteinFunctionSystem P
  field
    sequence     : Sequence
    conformation : Conformation
    environment₁ environment₂ : Environment
    partner₁ partner₂ : Partner
    modification : Modification
    localisation : Localisation
    history      : History

    FunctionsDiffer : Function → Function → Set
    contextChangesFunction :
      FunctionsDiffer
        (functionAt sequence conformation environment₁ partner₁
          modification localisation history)
        (functionAt sequence conformation environment₂ partner₂
          modification localisation history)
