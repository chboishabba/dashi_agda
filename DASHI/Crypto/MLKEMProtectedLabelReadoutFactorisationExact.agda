module DASHI.Crypto.MLKEMProtectedLabelReadoutFactorisationExact where

------------------------------------------------------------------------
-- ML-KEM: PROTECTED-LABEL READOUT FACTORISATION
--
-- PURPOSE
--
-- The missing information theorem should not start from candidate counts.  It
-- should start from the exact semantic requirement imposed on a verifier/readout
-- state: if the readout is sufficient to resolve a protected label, then the
-- protected-label map factors through the readout code.
--
--     Hidden --observe--> Code --decode--> Protected
--        \______________________________/
--                    protected
--
-- This module proves two consequences without any entropy/cardinality axiom:
--
--   1. equal readout codes force equal protected labels;
--   2. if every protected label has a hidden representative, then Protected
--      injects into Code.
--
-- The second statement is the exact finite-capacity seam we need: a bounded
-- code alphabet can resolve no more protected labels than it has distinct code
-- values.  Cardinality/bit accounting can be layered on afterwards.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong; trans; sym)

record ProtectedReadoutFactorisation : Set₁ where
  constructor protected-readout-factorisation
  field
    Hidden Protected Code : Set
    protected : Hidden → Protected
    observe : Hidden → Code
    decode : Code → Protected
    decodeCorrect : (hidden : Hidden) → decode (observe hidden) ≡ protected hidden

open ProtectedReadoutFactorisation public

------------------------------------------------------------------------
-- Readout equivalence is at least as fine as protected-label equivalence.
------------------------------------------------------------------------

sameReadoutForcesSameProtected :
  (factorisation : ProtectedReadoutFactorisation) →
  (left right : Hidden factorisation) →
  observe factorisation left ≡ observe factorisation right →
  protected factorisation left ≡ protected factorisation right
sameReadoutForcesSameProtected factorisation left right sameCode =
  trans
    (sym (decodeCorrect factorisation left))
    (trans
      (cong (decode factorisation) sameCode)
      (decodeCorrect factorisation right))

------------------------------------------------------------------------
-- If each protected label is actually represented by some hidden state, then
-- exact readout sufficiency embeds the protected-label carrier into Code.
------------------------------------------------------------------------

record RepresentedProtectedReadout : Set₁ where
  constructor represented-protected-readout
  field
    factorisation : ProtectedReadoutFactorisation
    representative :
      Protected factorisation → Hidden factorisation
    representativeCorrect :
      (label : Protected factorisation) →
      protected factorisation (representative label) ≡ label

open RepresentedProtectedReadout public

codeOfProtectedLabel :
  (represented : RepresentedProtectedReadout) →
  Protected (factorisation represented) →
  Code (factorisation represented)
codeOfProtectedLabel represented label =
  observe (factorisation represented) (representative represented label)

codeOfProtectedLabelDecodes :
  (represented : RepresentedProtectedReadout) →
  (label : Protected (factorisation represented)) →
  decode (factorisation represented) (codeOfProtectedLabel represented label)
  ≡ label
codeOfProtectedLabelDecodes represented label =
  trans
    (decodeCorrect
      (factorisation represented)
      (representative represented label))
    (representativeCorrect represented label)

codeOfProtectedLabelInjective :
  (represented : RepresentedProtectedReadout) →
  (left right : Protected (factorisation represented)) →
  codeOfProtectedLabel represented left ≡
    codeOfProtectedLabel represented right →
  left ≡ right
codeOfProtectedLabelInjective represented left right sameCode =
  trans
    (sym (codeOfProtectedLabelDecodes represented left))
    (trans
      (cong (decode (factorisation represented)) sameCode)
      (codeOfProtectedLabelDecodes represented right))

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- This is the representation-independent semantic core of the desired
-- refinement bound.  It does NOT yet say how many Code values exist or how
-- many bits/touches are needed to materialize/read them.  Those are separate
-- operational premises.
--
-- The high-alpha composition is now:
--
--   uncertainty -> touch/update lower bound
--   protected sufficiency -> Protected injects into Code
--   bounded code/readout capacity -> information/refinement lower bound.
------------------------------------------------------------------------
