module DASHI.Moonshine.Monster3BBarracloughWilson729SourceReceiptExact where

------------------------------------------------------------------------
-- BARRACLOUGH-WILSON SOURCE RECEIPT: THE 729 SCHRODINGER FACTOR, AND A
-- FIREWALL AROUND THE REPOSITORY'S MODEL Fin 90 MULTIPLICITY CARRIER
--
-- Primary source:
--   R. W. Barraclough and R. A. Wilson,
--   "The Character Table of a Maximal Subgroup of the Monster",
--   LMS J. Comput. Math. 10 (2007), 161-175,
--   DOI 10.1112/S1461157000001352.
--
-- Section 5.1 states that the extraspecial 3^(1+12) has two degree-729 complex
-- irreducible characters psi and conjugate-psi, and that both extend to
--
--     G = 3^(1+12) : 6.Suz.
--
-- The authors construct modular reductions of these representations over F31
-- in order to recover their complex character values.  This is strong external
-- alignment for the repository's 729-dimensional finite-Schrodinger factor.
-- It is still a SOURCE receipt, not a same-basis identification with the repo
-- `X6` basis.
--
-- Section 6 is a DIFFERENT induction lane.  Its subsection 6.4 says that its
-- U5(2):2-based computation assembles "90 more irreducible characters" of the
-- larger group.  That count is a count of irreducible characters produced by
-- that induction, not a theorem identifying the repository's `Fin 90`
-- multiplicity coordinate with a 90-dimensional module, a 90-element source
-- basis, or those 90 character labels.
--
-- This owner therefore records a deliberate firewall:
--
--   source degree-729 Heisenberg/Schrodinger alignment: YES;
--   actual W_zeta <-> X6 x Fin90 same-object recognition: NO;
--   "90 more irreducible characters" == model Fin90: NO.
--
-- The live representation seam remains an actual Base369RecognitionCandidate /
-- ActualZetaSectorRecognition on the selected literal Monster zeta sector.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

sourceTitle : String
sourceTitle = "The Character Table of a Maximal Subgroup of the Monster"

sourceDOI : String
sourceDOI = "10.1112/S1461157000001352"

degree729 : Nat
degree729 = 729

section6AdditionalCharacterCount : Nat
section6AdditionalCharacterCount = 90

record Boundary : Set where
  constructor boundary
  field
    sourceStatesTwoDegree729ExtraspecialCharacters : Bool
    sourceStatesBothExtendToSixSuzInertia : Bool
    sourceConstructsModularReductionsForCharacterEvaluation : Bool
    repoSchrodingerDimension729SourceAligned : Bool
    literal729BasisIntertwinerPaidByThisSourceReceipt : Bool
    sourceSection6AssemblesNinetyAdditionalIrreducibleCharacters : Bool
    section6NinetyCharactersIdentifiedWithModelFin90 : Bool
    actualWzetaToX6Fin90SameObjectPaid : Bool
    actualFin90MultiplicityActionPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    true true true true
    false
    true false
    false false
