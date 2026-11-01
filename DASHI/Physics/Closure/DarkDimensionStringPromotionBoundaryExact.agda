module DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Closure.EmpiricalCosmologyValidationBoundary as Cosmology
import DASHI.Physics.Closure.QuantumGravityTheoryBoundary as QuantumGravity

------------------------------------------------------------------------
-- DARK DIMENSION / STRING-THEORY PROMOTION BOUNDARY
--
-- The scientific chain is deliberately stratified:
--
-- string-theory framework
--   -> Swampland / Distance / Duality conjectural premises
--   -> Dark Dimension model
--   -> KK-graviton / evolving-dark-sector observables
--   -> cosmological or short-range-gravity tests.
--
-- A downstream model can be testable without being a necessary consequence of
-- the entire upstream framework.  Conversely, a positive downstream signal does
-- not identify its ultraviolet origin unless an independent uniqueness witness
-- is paid.  This module specializes the repository's existing empirical-
-- cosmology and quantum-gravity promotion boundaries; it does not create a new
-- quantum-gravity framework.
------------------------------------------------------------------------

data ClaimLayer : Set where
  stringTheoryFramework : ClaimLayer
  swamplandPremiseLayer : ClaimLayer
  darkDimensionModelLayer : ClaimLayer
  observableLayer : ClaimLayer
  empiricalTestLayer : ClaimLayer

record DarkDimensionPromotionStatus : Set where
  constructor darkDimensionPromotionStatus
  field
    swamplandMotivationAttributed : Bool
    observedDarkEnergyScaleUsed : Bool
    micronScaleConditionalPrediction : Bool
    kkDarkGravitonPhenomenologySpecified : Bool
    cosmologicalObservableSpecified : Bool
    modelHasFalsifiableTests : Bool
    currentDataConstrainModelParameters : Bool
    frameworkEntailsDarkDimensionModel : Bool
    darkDimensionNecessaryConsequenceOfStringTheory : Bool
    positiveSignalUniquelyIdentifiesStringTheory : Bool
    evolvingDarkEnergyUniquelyIdentifiesSwampland : Bool
    modelNullFalsifiesStringTheorySimpliciter : Bool
    stringTheoryPromotionPermitted : Bool
    statusScope : String

open DarkDimensionPromotionStatus public

canonicalDarkDimensionPromotionStatus : DarkDimensionPromotionStatus
canonicalDarkDimensionPromotionStatus =
  darkDimensionPromotionStatus
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    "the Dark Dimension is a falsifiable Swampland-motivated model family; model testability and parameter constraints do not by themselves pay framework entailment, unique ultraviolet identification, or string-theory promotion"

------------------------------------------------------------------------
-- Positive content retained without over-promotion.
------------------------------------------------------------------------

darkDimensionModelTestable :
  modelHasFalsifiableTests canonicalDarkDimensionPromotionStatus ≡ true
darkDimensionModelTestable = refl

micronScaleIsConditionalOnSwamplandPremises :
  micronScaleConditionalPrediction canonicalDarkDimensionPromotionStatus ≡ true
micronScaleIsConditionalOnSwamplandPremises = refl

currentCosmologyConstrainsModelParameters :
  currentDataConstrainModelParameters canonicalDarkDimensionPromotionStatus ≡ true
currentCosmologyConstrainsModelParameters = refl

------------------------------------------------------------------------
-- Promotion witnesses.  These are intentionally stronger than mere model
-- testability.  The canonical status does not inhabit them.
------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

record StringTheoryPromotionWitness
    (status : DarkDimensionPromotionStatus) : Set where
  constructor stringTheoryPromotionWitness
  field
    entailmentPaid : frameworkEntailsDarkDimensionModel status ≡ true
    uniqueOriginPaid : positiveSignalUniquelyIdentifiesStringTheory status ≡ true

open StringTheoryPromotionWitness public

record PositiveSignalStringIdentityWitness
    (status : DarkDimensionPromotionStatus) : Set where
  constructor positiveSignalStringIdentityWitness
  field
    positiveSignalUniquenessPaid :
      positiveSignalUniquelyIdentifiesStringTheory status ≡ true

open PositiveSignalStringIdentityWitness public

record StringTheoryFalsificationWitness
    (status : DarkDimensionPromotionStatus) : Set where
  constructor stringTheoryFalsificationWitness
  field
    necessityPaid :
      darkDimensionNecessaryConsequenceOfStringTheory status ≡ true

open StringTheoryFalsificationWitness public

record SwamplandIdentityWitness
    (status : DarkDimensionPromotionStatus) : Set where
  constructor swamplandIdentityWitness
  field
    evolvingDarkEnergyUniquenessPaid :
      evolvingDarkEnergyUniquelyIdentifiesSwampland status ≡ true

open SwamplandIdentityWitness public

modelTestabilityDoesNotPromoteStringTheory :
  StringTheoryPromotionWitness canonicalDarkDimensionPromotionStatus → ⊥
modelTestabilityDoesNotPromoteStringTheory witness =
  false≢true (entailmentPaid witness)

positiveSignalDoesNotUniquelyIdentifyStringTheory :
  PositiveSignalStringIdentityWitness canonicalDarkDimensionPromotionStatus → ⊥
positiveSignalDoesNotUniquelyIdentifyStringTheory witness =
  false≢true (positiveSignalUniquenessPaid witness)

modelNullDoesNotFalsifyStringTheorySimpliciter :
  StringTheoryFalsificationWitness canonicalDarkDimensionPromotionStatus → ⊥
modelNullDoesNotFalsifyStringTheorySimpliciter witness =
  false≢true (necessityPaid witness)

evolvingDarkEnergyDoesNotUniquelyIdentifySwampland :
  SwamplandIdentityWitness canonicalDarkDimensionPromotionStatus → ⊥
evolvingDarkEnergyDoesNotUniquelyIdentifySwampland witness =
  false≢true (evolvingDarkEnergyUniquenessPaid witness)

stringTheoryPromotionBlocked :
  stringTheoryPromotionPermitted canonicalDarkDimensionPromotionStatus ≡ false
stringTheoryPromotionBlocked = refl

------------------------------------------------------------------------
-- Existing repository boundaries remain authoritative downstream consumers.
------------------------------------------------------------------------

theoryOfEverythingPromotionStillBlocked :
  QuantumGravity.theoryOfEverythingClaimPermitted
    QuantumGravity.canonicalQuantumGravityPromotionBoundary
  ≡ false
theoryOfEverythingPromotionStillBlocked =
  QuantumGravity.canonicalTheoryOfEverythingBlocked

empiricalCosmologyPromotionStillRequiresFullReceipt :
  Cosmology.empiricalCosmologyClaimPermitted
    Cosmology.canonicalEmpiricalCosmologyPromotionBoundary
  ≡ false
empiricalCosmologyPromotionStillRequiresFullReceipt =
  Cosmology.canonicalEmpiricalCosmologyBlocked

------------------------------------------------------------------------
-- Source atlas.  Citation pays source identity and the bounded relationship
-- stated here; it imports neither proof nor scientific authority.
------------------------------------------------------------------------

monteroVafaValenzuela2023 : Source.AttributedSource
monteroVafaValenzuela2023 =
  Source.mkDOISource
    "Miguel Montero; Cumrun Vafa; Irene Valenzuela"
    "The dark dimension and the Swampland"
    "Journal of High Energy Physics 2023, 22"
    "2023"
    "10.1007/JHEP02(2023)022"
    "https://doi.org/10.1007/JHEP02(2023)022"
    Source.academicArticleSource
    "source for the conditional Distance/Duality + observed-dark-energy route to a mesoscopic extra dimension; source wording does not manufacture unconditional entailment from string theory simpliciter"
    Source.publicAttribution

gonzaloMonteroObiedVafa2023 : Source.AttributedSource
gonzaloMonteroObiedVafa2023 =
  Source.mkDOISource
    "Eduardo Gonzalo; Miguel Montero; Georges Obied; Cumrun Vafa"
    "Dark dimension gravitons as dark matter"
    "Journal of High Energy Physics 2023, 109"
    "2023"
    "10.1007/JHEP11(2023)109"
    "https://doi.org/10.1007/JHEP11(2023)109"
    Source.academicArticleSource
    "source for KK spin-2 dark-graviton phenomenology inside the Dark Dimension scenario"
    Source.publicAttribution

obiedDvorkinGonzaloVafa2024 : Source.AttributedSource
obiedDvorkinGonzaloVafa2024 =
  Source.mkDOISource
    "Georges Obied; Cora Dvorkin; Eduardo Gonzalo; Cumrun Vafa"
    "Dark dimension and decaying dark matter gravitons"
    "Physical Review D 109, 063540"
    "2024"
    "10.1103/PhysRevD.109.063540"
    "https://doi.org/10.1103/PhysRevD.109.063540"
    Source.academicArticleSource
    "source for cosmological constraints and near-future signatures of decaying dark gravitons; parameter constraint is kept distinct from ultraviolet-framework identification"
    Source.publicAttribution

pourtsidou2026 : Source.AttributedSource
pourtsidou2026 =
  Source.mkDOISource
    "Alkistis Pourtsidou"
    "Testing String Theory with Combined Cosmological Probes: A Case Study for Dark Matter Gravitons"
    "Research Notes of the AAS 10(7), 190"
    "2026"
    "10.3847/2515-5172/ae8906"
    "https://doi.org/10.3847/2515-5172/ae8906"
    Source.academicArticleSource
    "source for current CMB/BAO constraints and Stage-IV forecast language; the formalisation narrows the referent to Dark-Dimension dark-sector models rather than string theory simpliciter"
    Source.publicAttribution

bedroyaObiedVafaWu2026 : Source.AttributedSource
bedroyaObiedVafaWu2026 =
  Source.mkDOISource
    "Alek Bedroya; Georges Obied; Cumrun Vafa; David H. Wu"
    "Evolving dark sector and the dark dimension scenario"
    "Physical Review D, accepted 3 August 2026"
    "2026"
    "10.1103/1rsq-cv2m"
    "https://doi.org/10.1103/1rsq-cv2m"
    Source.academicArticleSource
    "source for a coupled evolving-dark-energy / evolving-dark-matter realization; empirical preference inside this model does not uniquely identify Swampland premises"
    Source.publicAttribution

darkDimensionSourceAtlas : Source.AttributedSourceAtlas
darkDimensionSourceAtlas =
  Source.mkSourceAtlas
    "Dark Dimension / string-promotion boundary source atlas"
    "DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact"
    ( monteroVafaValenzuela2023
    ∷ gonzaloMonteroObiedVafa2023
    ∷ obiedDvorkinGonzaloVafa2024
    ∷ pourtsidou2026
    ∷ bedroyaObiedVafaWu2026
    ∷ [])
    "source-bound attribution for the Dark Dimension motivation, dark-graviton phenomenology, cosmological constraints, and evolving-dark-sector continuation; citations do not promote model tests into proof of string theory"
