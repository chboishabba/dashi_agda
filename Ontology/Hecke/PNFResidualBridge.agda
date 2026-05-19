module Ontology.Hecke.PNFResidualBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; _∷_; [])
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality as Eq using (cong; sym; trans)

open import DASHI.Interop.SensibLawResidualLattice using
  ( ResidualLevel
  ; exact ; partial ; noTypedMeet ; contradiction
  ; StructuralSignature
  ; residualToPressure
  ; residualSeverity
  ; joinResidual
  )
open import DASHI.Pressure using (Pressure; critical)
open import Ontology.Hecke.QuotientRepresentation using (QuotientInterfaceOn)

------------------------------------------------------------------------
-- PNF-facing bridge for Hecke quotient fibres.
--
-- This is deliberately a bridge/adapter module.  It does not import runtime
-- ITIR/SensibLaw parsing and it does not claim that a Hecke support pattern is
-- itself a text predicate.  It states the reusable typed correspondence:
-- quotient-projection equality is the candidate fibre, and defect classes
-- embed into the already proved PNF residual chain.

data HeckeDefectClass : Set where
  stableDefect : HeckeDefectClass
  illegalDefect : HeckeDefectClass
  otherDefect : HeckeDefectClass

record HeckeDefectHistogram : Set where
  constructor heckeDefectHistogram
  field
    stableCount : Nat
    illegalCount : Nat
    otherCount : Nat

open HeckeDefectHistogram public

canonicalSaturatedHeckeHistogram : HeckeDefectHistogram
canonicalSaturatedHeckeHistogram = heckeDefectHistogram 15 zero zero

defectResidual : HeckeDefectClass → ResidualLevel
defectResidual stableDefect = partial
defectResidual illegalDefect = contradiction
defectResidual otherDefect = noTypedMeet

defectResidual-stable : defectResidual stableDefect ≡ partial
defectResidual-stable = refl

defectResidual-illegal : defectResidual illegalDefect ≡ contradiction
defectResidual-illegal = refl

defectResidual-other : defectResidual otherDefect ≡ noTypedMeet
defectResidual-other = refl

illegalDefect-critical :
  residualToPressure (defectResidual illegalDefect) ≡ critical
illegalDefect-critical = refl

illegalDefect-maxSeverity :
  residualSeverity (defectResidual illegalDefect) ≡ 9
illegalDefect-maxSeverity = refl

joinResidual-illegal-left :
  ∀ d →
  joinResidual (defectResidual illegalDefect) (defectResidual d)
    ≡ contradiction
joinResidual-illegal-left stableDefect = refl
joinResidual-illegal-left illegalDefect = refl
joinResidual-illegal-left otherDefect = refl

joinResidual-illegal-right :
  ∀ d →
  joinResidual (defectResidual d) (defectResidual illegalDefect)
    ≡ contradiction
joinResidual-illegal-right stableDefect = refl
joinResidual-illegal-right illegalDefect = refl
joinResidual-illegal-right otherDefect = refl

histogramDefectClass : HeckeDefectHistogram → HeckeDefectClass
histogramDefectClass h with illegalCount h | otherCount h | stableCount h
... | suc _ | _ | _ = illegalDefect
... | zero | suc _ | _ = otherDefect
... | zero | zero | _ = stableDefect

histogramResidual : HeckeDefectHistogram → ResidualLevel
histogramResidual h = defectResidual (histogramDefectClass h)

canonicalSaturatedHistogram-residual :
  histogramResidual canonicalSaturatedHeckeHistogram ≡ partial
canonicalSaturatedHistogram-residual = refl

------------------------------------------------------------------------
-- Hecke quotient fibre as a PNF candidate pool.

SameHeckeCandidatePool :
  ∀ {S Class : Set} →
  QuotientInterfaceOn S Class →
  S → S → Set
SameHeckeCandidatePool q x y =
  QuotientInterfaceOn.proj q x ≡ QuotientInterfaceOn.proj q y

sameCandidatePool-refl :
  ∀ {S Class : Set}
    (q : QuotientInterfaceOn S Class)
    (x : S) →
  SameHeckeCandidatePool q x x
sameCandidatePool-refl q x = refl

sameCandidatePool-sym :
  ∀ {S Class : Set}
    (q : QuotientInterfaceOn S Class)
    {x y : S} →
  SameHeckeCandidatePool q x y →
  SameHeckeCandidatePool q y x
sameCandidatePool-sym q xy = sym xy

sameCandidatePool-trans :
  ∀ {S Class : Set}
    (q : QuotientInterfaceOn S Class)
    {x y z : S} →
  SameHeckeCandidatePool q x y →
  SameHeckeCandidatePool q y z →
  SameHeckeCandidatePool q x z
sameCandidatePool-trans q xy yz = trans xy yz

supportFibreToPNFSignature :
  ∀ {S Class : Set}
    (q : QuotientInterfaceOn S Class)
    (classToSignature : Class → StructuralSignature)
    {x y : S} →
  SameHeckeCandidatePool q x y →
  classToSignature (QuotientInterfaceOn.proj q x)
    ≡ classToSignature (QuotientInterfaceOn.proj q y)
supportFibreToPNFSignature q classToSignature xy = cong classToSignature xy

record HeckePNFResidualBridgeSurface : Set₁ where
  field
    defectCarrier : Set
    defectToResidual : HeckeDefectClass → ResidualLevel
    illegalIsContradiction :
      defectToResidual illegalDefect ≡ contradiction
    illegalPressureMax :
      residualToPressure (defectToResidual illegalDefect) ≡ critical
    saturatedBranchResidual :
      histogramResidual canonicalSaturatedHeckeHistogram ≡ partial
    candidatePoolCarrier :
      ∀ {S Class : Set} →
      QuotientInterfaceOn S Class →
      S → S → Set
    candidatePoolSoundForPNF :
      ∀ {S Class : Set}
        (q : QuotientInterfaceOn S Class)
        (classToSignature : Class → StructuralSignature)
        {x y : S} →
      candidatePoolCarrier q x y →
      classToSignature (QuotientInterfaceOn.proj q x)
        ≡ classToSignature (QuotientInterfaceOn.proj q y)
    nonClaimBoundary : List String

heckePNFResidualBridgeSurface : HeckePNFResidualBridgeSurface
heckePNFResidualBridgeSurface =
  record
    { defectCarrier = HeckeDefectClass
    ; defectToResidual = defectResidual
    ; illegalIsContradiction = defectResidual-illegal
    ; illegalPressureMax = illegalDefect-critical
    ; saturatedBranchResidual = canonicalSaturatedHistogram-residual
    ; candidatePoolCarrier = SameHeckeCandidatePool
    ; candidatePoolSoundForPNF = supportFibreToPNFSignature
    ; nonClaimBoundary =
        "Hecke quotient projection equality is only a candidate-pool fibre, not runtime text evidence"
        ∷ "Defect classes embed into PNF residual pressure; they do not create PredicatePNF atoms"
        ∷ "The saturated histogram maps to partial forced-stable residual, not exact equivalence"
        ∷ "Runtime spaCy/ITIR parser output still requires a future receipt-bearing consumer"
        ∷ []
    }
