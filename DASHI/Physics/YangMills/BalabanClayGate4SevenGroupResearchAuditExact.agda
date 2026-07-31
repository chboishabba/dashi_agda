module DASHI.Physics.YangMills.BalabanClayGate4SevenGroupResearchAuditExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary and methodological source audit for the seven remaining physical
-- groups.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
-- Published June 1987.
--
-- This is the primary theorem source for the four-dimensional small-field RG
-- convention, localized effective actions and coupling recursion.  It does not
-- provide DASHI's concrete periodic lists, finite coordinate basis or matrix
-- representation; those are repository-specific constructions.
--
-- Hans Koch and Peter Wittwer,
-- "A Non-Gaussian Renormalization Group Fixed Point for Hierarchical Scalar
-- Lattice Field Theories",
-- Communications in Mathematical Physics 106 (3) (1986), 495--532.
-- DOI: 10.1007/BF01207260.
--
-- Hans Koch and Peter Wittwer,
-- "On the Renormalization Group Transformation for Scalar Hierarchical
-- Models",
-- Communications in Mathematical Physics 138 (1991), 537--568.
-- DOI: 10.1007/BF02102041.
--
-- These are methodological precedents for an RG proof that retains explicit
-- contraction and correction budgets.  Neither paper proves a Yang--Mills
-- Q-star estimate or identifies Bałaban's physical weights.
--
-- Hans Koch, Alain Schenkel and Peter Wittwer,
-- "Computer-Assisted Proofs in Analysis and Programming in Logic: A Case
-- Study", mp_arc 94-394 (1994); no DOI recorded.
--
-- The public file commonly named prolog.pdf belongs to this separate
-- computer-assisted proof case study.  It must not be cited as though it were
-- the 1986 hierarchical scalar fixed-point paper.  Its contraction/residual
-- organisation may be used only as computer-assisted methodology.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- Ilse C. F. Ipsen and Rizwana Rehman,
-- "Perturbation Bounds for Determinants and Characteristic Polynomials",
-- SIAM Journal on Matrix Analysis and Applications 30 (2008), 762--776.
-- DOI: 10.1137/070704770.
------------------------------------------------------------------------

data SourceAuthority : Set where
  primaryYangMills : SourceAuthority
  standardMathematics : SourceAuthority
  methodologicalPrecedent : SourceAuthority
  empiricalCorroboration : SourceAuthority
  locatorOnly : SourceAuthority

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    title author identifier : String
    authority : SourceAuthority
    mayClosePhysicalYangMillsInput : Bool

open SourceReceipt public

balabanCMP109Receipt : SourceReceipt
balabanCMP109Receipt = sourceReceipt
  "Renormalization Group Approach to Lattice Gauge Field Theories. I. Generation of Effective Actions in a Small Field Approximation and a Coupling Constant Renormalization in Four Dimensions"
  "Tadeusz Balaban"
  "CMP 109(2), 249--301 (June 1987); DOI 10.1007/BF01215223"
  primaryYangMills true

kochWittwer1986Receipt : SourceReceipt
kochWittwer1986Receipt = sourceReceipt
  "A Non-Gaussian Renormalization Group Fixed Point for Hierarchical Scalar Lattice Field Theories"
  "Hans Koch and Peter Wittwer"
  "CMP 106(3), 495--532 (1986); DOI 10.1007/BF01207260"
  methodologicalPrecedent false

kochWittwer1991Receipt : SourceReceipt
kochWittwer1991Receipt = sourceReceipt
  "On the Renormalization Group Transformation for Scalar Hierarchical Models"
  "Hans Koch and Peter Wittwer"
  "CMP 138, 537--568 (1991); DOI 10.1007/BF02102041"
  methodologicalPrecedent false

kochSchenkelWittwerPrologReceipt : SourceReceipt
kochSchenkelWittwerPrologReceipt = sourceReceipt
  "Computer-Assisted Proofs in Analysis and Programming in Logic: A Case Study"
  "Hans Koch, Alain Schenkel and Peter Wittwer"
  "mp_arc 94-394 (1994); no DOI recorded"
  methodologicalPrecedent false

hornJohnsonReceipt : SourceReceipt
hornJohnsonReceipt = sourceReceipt
  "Matrix Analysis, Second Edition"
  "Roger A. Horn and Charles R. Johnson"
  "Cambridge University Press (2012); DOI 10.1017/CBO9781139020411"
  standardMathematics false

ipsenRehmanReceipt : SourceReceipt
ipsenRehmanReceipt = sourceReceipt
  "Perturbation Bounds for Determinants and Characteristic Polynomials"
  "Ilse C. F. Ipsen and Rizwana Rehman"
  "SIAM J. Matrix Anal. Appl. 30, 762--776 (2008); DOI 10.1137/070704770"
  standardMathematics false

balabanCMP109MetadataLevel : ProofLevel
balabanCMP109MetadataLevel = standardImported

kochWittwer1986MetadataLevel : ProofLevel
kochWittwer1986MetadataLevel = standardImported

kochWittwer1991MetadataLevel : ProofLevel
kochWittwer1991MetadataLevel = standardImported

prologCaseStudySeparationLevel : ProofLevel
prologCaseStudySeparationLevel = standardImported

hierarchicalContractionArchitectureTransferLevel : ProofLevel
hierarchicalContractionArchitectureTransferLevel = conditional

hierarchicalScalarPaperProvesYangMillsKernelEstimate : ProofLevel
hierarchicalScalarPaperProvesYangMillsKernelEstimate = conjectural

sevenPhysicalGroupsRequireRepositoryOrPrimaryInputs : Bool
sevenPhysicalGroupsRequireRepositoryOrPrimaryInputs = true
