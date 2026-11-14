module DASHI.Physics.Chemistry.BemethylChemicalIdentityBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record BemethylChemicalIdentity : Set where
  field
    neutralFormula : String
    neutralCompoundName : String
    historicalSaltForm : String
    benzimidazoleCorePresent : Bool
    sulfurSubstituentPresent : Bool

    isPurineBase : Bool
    sameMoleculeAsAdenine : Bool
    sameMoleculeAsGuanine : Bool
    structuralSimilarityProvesGenomicTarget : Bool
    saltIdentityEqualsNeutralIdentity : Bool

open BemethylChemicalIdentity public

canonicalBemethylChemicalIdentity : BemethylChemicalIdentity
canonicalBemethylChemicalIdentity = record
  { neutralFormula = "C9H10N2S"
  ; neutralCompoundName = "2-(ethylthio)-1H-benzimidazole / bemethyl parent"
  ; historicalSaltForm = "bemethyl/bemitil hydrobromide formulation reported in actoprotector literature"
  ; benzimidazoleCorePresent = true
  ; sulfurSubstituentPresent = true
  ; isPurineBase = false
  ; sameMoleculeAsAdenine = false
  ; sameMoleculeAsGuanine = false
  ; structuralSimilarityProvesGenomicTarget = false
  ; saltIdentityEqualsNeutralIdentity = false
  }

notAPurine : isPurineBase canonicalBemethylChemicalIdentity ≡ false
notAPurine = refl

similarityNotTarget :
  structuralSimilarityProvesGenomicTarget canonicalBemethylChemicalIdentity ≡ false
similarityNotTarget = refl

saltParentSeparated :
  saltIdentityEqualsNeutralIdentity canonicalBemethylChemicalIdentity ≡ false
saltParentSeparated = refl
