module DASHI.Promotion.TranslationContextCategoricalLoom where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ProjectionHomology as PH
import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ProjectionConstructor as PCON

import DASHI.Promotion.TranslationContextEncoding as TC

----------------------------------------------------------------------
-- Translation context: categorical upgrade.
--
-- Grammar = MolecularContext (canonical, mitochondrial, ciliate, ...)
-- Each context determines a Codon -> ProteinSymbol translation map.
--
-- Objects:
--   inputCodon    : the codon space (domain of translation)
--   outputSymbol  : the protein-symbol space (codomain of translation)
--
-- Morphisms: functions between codon/protein-symbol spaces.
--
-- Fibre(tau_ctx, ps) = { c : Codon | tau_ctx c ≡ ps }
--   Canonical: tau^{-1}(Met) = {ATG}
--   Mitochondrial: tau^{-1}(Met) = {ATG, ATA}
--   The fibre changes across grammar contexts.
----------------------------------------------------------------------

data TCObj : Set where
  inputCodon    : TCObj
  outputSymbol  : TCObj

Underlying : TCObj -> Set
Underlying inputCodon    = TC.Codon
Underlying outputSymbol  = TC.ProteinSymbol

tcProjectionCategory : TC.MolecularContext -> PC.ProjectionCategory
tcProjectionCategory ctx = record
  { Obj             = TCObj
  ; Hom             = λ A B -> Underlying A -> Underlying B
  ; id              = λ x -> x
  ; _∘_             = λ g f x -> g (f x)
  ; id-left         = λ f -> refl
  ; id-right        = λ f -> refl
  ; assoc           = λ f g h -> refl
  ; categoryReading = "Pi_TC(translation context)"
  }

tcGrammarCategory : GGC.GrammarGeneratedCategory
tcGrammarCategory = record
  { Grammar        = TC.MolecularContext
  ; 𝓟              = tcProjectionCategory
  ; grammarReading = "Gamma_TC = MolecularContext"
  }

----------------------------------------------------------------------
-- Fibre of tau_ctx over a protein symbol
----------------------------------------------------------------------

fibreOverSymbol : (ctx : TC.MolecularContext) (ps : TC.ProteinSymbol) -> Set
fibreOverSymbol ctx ps = Σ TC.Codon λ c -> TC.τMolec ctx c ≡ ps

----------------------------------------------------------------------
-- Constructor: translation as biological process
----------------------------------------------------------------------

constructTC : {A B : TCObj} (ctx : TC.MolecularContext)
            -> (Underlying A -> Underlying B)
constructTC {inputCodon} {outputSymbol} ctx = TC.τMolec ctx
constructTC {inputCodon} {inputCodon} ctx   = λ x -> x
constructTC {outputSymbol} {inputCodon} ctx = λ _ -> TC.codon TC.A TC.A TC.A
constructTC {outputSymbol} {outputSymbol} ctx = λ x -> x

tcConstructor : PCON.ProjectionConstructor
  (tcProjectionCategory TC.canonicalMolecularContext)
tcConstructor = record
  { MethodCarrier = TC.MolecularContext
  ; construct     = constructTC
  ; methodKind    = "genetic code translation: codon -> protein"
  }
