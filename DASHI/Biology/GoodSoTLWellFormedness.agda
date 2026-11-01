module DASHI.Biology.GoodSoTLWellFormedness where

open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- FELTEN'S PRINCIPLES AS WELL-FORMEDNESS OBLIGATIONS
--
-- Reference:
--   Peter Felten,
--   "Principles of good practice in SoTL",
--   Teaching & Learning Inquiry 1(1), 121-125 (2013).
--   DOI: 10.20343/teachlearninqu.1.1.121.
--
-- Felten names five guideposts: inquiry into student learning, grounded in
-- context, methodologically sound, conducted in partnership with students, and
-- appropriately public.  DASHI does not identify those five principles with
-- the entire epistemic object; instead they become application-supplied
-- well-formedness obligations over a concrete inquiry.
------------------------------------------------------------------------

record GoodSoTLObligations (Inquiry : Set) : Set₁ where
  constructor goodSoTLObligations
  field
    LearnerDirected : Inquiry → Set
    ContextGrounded : Inquiry → Set
    MethodologicallySound : Inquiry → Set
    PartnershipAdequate : Inquiry → Set
    AppropriatelyPublic : Inquiry → Set

open GoodSoTLObligations public

record GoodSoTL
    {Inquiry : Set}
    (obligations : GoodSoTLObligations Inquiry)
    (inquiry : Inquiry) : Set₁ where
  constructor goodSoTL
  field
    learnerDirected : LearnerDirected obligations inquiry
    contextGrounded : ContextGrounded obligations inquiry
    methodologicallySound : MethodologicallySound obligations inquiry
    partnershipAdequate : PartnershipAdequate obligations inquiry
    appropriatelyPublic : AppropriatelyPublic obligations inquiry
    receipt : String

open GoodSoTL public
