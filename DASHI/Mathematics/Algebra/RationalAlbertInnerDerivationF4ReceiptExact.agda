module DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationF4ReceiptExact where

------------------------------------------------------------------------
-- ALBERT INNER DERIVATIONS: EXACT 52-DIMENSIONAL EXECUTABLE RECEIPT
--
-- The concrete rational Albert algebra is owned upstream.  The companion
-- executable
--
--   scripts/albert_inner_derivation_rank.py
--
-- reconstructs the same 27-coordinate Jordan structure constants after
-- clearing the factor 1/2.  It then computes every nonzero commutator
--
--   [L_ei,L_ej]
--
-- of coordinate-basis left multiplications.  Exact integer arithmetic checks
-- the derivation law on all 27^2 basis products for every nonzero commutator.
-- SymPy's exact ZZ DomainMatrix rank gives 52 for their 729-coordinate matrix
-- span.
--
-- This file records that executable result separately from the classification
-- theorem.  Dimension 52 by itself is NOT used to infer F4.  Standard Albert
-- algebra theory identifies Der(H_3(O)) with a form of the simple Lie algebra
-- of type F4; that classification is source-backed rather than reproved here.
--
-- Background sources used by the surrounding algebra lane:
--   Richard D. Schafer, An Introduction to Nonassociative Algebras (1966).
--   Nathan Jacobson, Structure and Representations of Jordan Algebras (1968).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J
import DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact as Laws

------------------------------------------------------------------------
-- Concrete inner-derivation operator target on the actual Albert carrier.
------------------------------------------------------------------------

innerDerivation : A.RationalAlbert → A.RationalAlbert → A.RationalAlbert → A.RationalAlbert
innerDerivation x y z =
  A._+A_
    (J.jordanProduct x (J.jordanProduct y z))
    (A.negA (J.jordanProduct y (J.jordanProduct x z)))

InnerDerivationLaw : Set
InnerDerivationLaw =
  (x y u v : A.RationalAlbert) →
    innerDerivation x y (J.jordanProduct u v)
    ≡ A._+A_
        (J.jordanProduct (innerDerivation x y u) v)
        (J.jordanProduct u (innerDerivation x y v))
  where
    open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Executable exact-linear-algebra receipt.
------------------------------------------------------------------------

record InnerDerivationExecutableReceipt : Set where
  constructor inner-derivation-executable-receipt
  field
    scriptPath : String
    coordinateDimension : Nat
    basisProductsChecked : Nat
    nonzeroInnerCommutators : Nat
    allBasisDerivationIdentitiesExact : Bool
    exactRationalSpanRank : Nat
    modularOnly : Bool
open InnerDerivationExecutableReceipt public

canonicalInnerDerivationExecutableReceipt : InnerDerivationExecutableReceipt
canonicalInnerDerivationExecutableReceipt =
  inner-derivation-executable-receipt
    "scripts/albert_inner_derivation_rank.py"
    27
    729
    324
    true
    52
    false

------------------------------------------------------------------------
-- Classification receipt.  Keep source theorem authority separate from the
-- executable rank certificate.
------------------------------------------------------------------------

record AlbertF4ClassificationReceipt : Set where
  constructor albert-f4-classification-receipt
  field
    concreteRationalAlbertCarrierSourceWritten : Bool
    concreteJordanProductSourceWritten : Bool
    concreteJordanIdentitySourceWritten : Bool
    exactInnerDerivationRank52Executed : Bool
    classificationSource : String
    sourceStatesDerivationAlgebraTypeF4 : Bool
    internalDynkinClassificationReprovedHere : Bool
    fullAutomorphismGroupSchemeConstructedHere : Bool
open AlbertF4ClassificationReceipt public

canonicalAlbertF4ClassificationReceipt : AlbertF4ClassificationReceipt
canonicalAlbertF4ClassificationReceipt =
  albert-f4-classification-receipt
    true
    true
    true
    true
    "Schafer/Jacobson: derivation algebra of the Albert algebra is a form of type F4"
    true
    false
    false

record Boundary : Set where
  constructor boundary
  field
    actualInnerDerivationOperatorTyped : Bool
    exact324CommutatorAuditInstalled : Bool
    allBasisDerivationChecksPaidByExactProducer : Bool
    exactRationalRank52PaidByProducer : Bool
    rankAloneUsedToInferF4 : Bool
    sourceBackedF4DerivationClassificationRecorded : Bool
    fullF4AutomorphismGroupConstructed : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true false true false
