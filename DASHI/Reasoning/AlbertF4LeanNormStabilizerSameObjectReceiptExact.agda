module DASHI.Reasoning.AlbertF4LeanNormStabilizerSameObjectReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER RECEIPT: Lean #52 native Albert norm-stabilizer/Jordan weld
--
-- Companion Lean source writes, on its literal rational Albert carrier:
--
--   unit-fixing cubic-norm symmetry membership
--      iff
--   Jordan-automorphism membership
--
-- for the same underlying rational linear bijection, with the actual forward
-- and backward actions preserved by the two translations.
--
-- Attribution / authority boundary:
-- * the concrete same-object/action theorem is DASHI Lean work;
-- * Petersson / Alsaody / Garibaldi--Petersson--Racine retain authorship of the
--   external characteristic-zero F4/E6 classification theorems;
-- * this Agda file is a receipt only and transfers no Lean kernel theorem;
-- * the original-Q-form algebraic-group classification remains formally open
--   here unless separately proved in the Agda kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

record LeanNormStabilizerJordanReceipt : Set where
  constructor lean-norm-stabilizer-jordan-receipt
  field
    sameLiteralRationalAlbertCarrier : Bool
    normUnitRigiditySourceWrittenInLean : Bool
    sameForwardBackwardActionPreserved : Bool
    normUnitMembershipIffJordanMembershipSourceWrittenInLean : Bool
    externalClassificationAuthorsPreserved : Bool
    externalSourceTheoremAttributedToDASHI : Bool
    crossKernelProofAuthorityTransferred : Bool
    AgdaOriginalQFormF4ClassificationPaid : Bool
    AgdaOriginalQFormE6ClassificationPaid : Bool
open LeanNormStabilizerJordanReceipt public

canonicalReceipt : LeanNormStabilizerJordanReceipt
canonicalReceipt = lean-norm-stabilizer-jordan-receipt
  true true true true true
  false false
  false false
