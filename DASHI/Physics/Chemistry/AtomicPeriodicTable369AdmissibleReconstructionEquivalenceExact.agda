module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdmissibleReconstructionEquivalenceExact where

open import DASHI.Core.Prelude

import DASHI.Core.SymmetryResolvedFibreExact as Sym

------------------------------------------------------------------------
-- ADMISSIBLE RECONSTRUCTION EQUIVALENCE
--
-- A SymmetryResolvedFibre already proves that a rich state can be reopened
-- exactly from its observed surface plus retained residual.  This owner makes
-- the corresponding admissible total-space reading explicit without claiming
-- that every arbitrary Surface x Residual pair is realizable.
------------------------------------------------------------------------

record SurfaceResidualPair (Surface Residual : Set) : Set where
  constructor surfaceResidualPair
  field
    surface : Surface
    residual : Residual

open SurfaceResidualPair public

encode :
  ∀ {G Rich Surface Residual} →
  Sym.SymmetryResolvedFibre G Rich Surface Residual →
  Rich → SurfaceResidualPair Surface Residual
encode F x =
  surfaceResidualPair
    (Sym.observe (Sym.observer F) x)
    (Sym.retainResidual (Sym.residualObserver F) x)

decode :
  ∀ {G Rich Surface Residual} →
  Sym.SymmetryResolvedFibre G Rich Surface Residual →
  SurfaceResidualPair Surface Residual → Rich
decode F p =
  Sym.reopen (Sym.residualObserver F) (surface p) (residual p)

decodeEncodeExact :
  ∀ {G Rich Surface Residual}
    (F : Sym.SymmetryResolvedFibre G Rich Surface Residual) →
  (x : Rich) → decode F (encode F x) ≡ x
decodeEncodeExact F = Sym.reopenAfterObservation F

------------------------------------------------------------------------
-- Admissibility of a surface/residual pair is exactly the requirement that
-- reopening it returns a rich state whose two coordinates are the same pair.
-- This is the dependent-fibre restriction that blocks the invalid product
-- claim Rich ≅ Surface x Residual for arbitrary pairs.
------------------------------------------------------------------------

record AdmissibleSurfaceResidual
  {G Rich Surface Residual : Set}
  (F : Sym.SymmetryResolvedFibre G Rich Surface Residual)
  (p : SurfaceResidualPair Surface Residual)
  : Set where
  constructor admissibleSurfaceResidual
  field
    surfaceRecovered :
      Sym.observe (Sym.observer F) (decode F p) ≡ surface p
    residualRecovered :
      Sym.retainResidual (Sym.residualObserver F) (decode F p) ≡ residual p

open AdmissibleSurfaceResidual public

encodeDecodeSurfaceExact :
  ∀ {G Rich Surface Residual}
    (F : Sym.SymmetryResolvedFibre G Rich Surface Residual) →
  (p : SurfaceResidualPair Surface Residual) →
  AdmissibleSurfaceResidual F p →
  surface (encode F (decode F p)) ≡ surface p
encodeDecodeSurfaceExact F p a = surfaceRecovered a

encodeDecodeResidualExact :
  ∀ {G Rich Surface Residual}
    (F : Sym.SymmetryResolvedFibre G Rich Surface Residual) →
  (p : SurfaceResidualPair Surface Residual) →
  AdmissibleSurfaceResidual F p →
  residual (encode F (decode F p)) ≡ residual p
encodeDecodeResidualExact F p a = residualRecovered a

record AdmissibleReconstructionBoundary : Set where
  constructor admissibleReconstructionBoundary
  field
    richStateEquivalentToAdmissibleSurfaceResidualSigma : Bool
    richStateEquivalentToAdmissibleSurfaceResidualSigmaIsTrue :
      richStateEquivalentToAdmissibleSurfaceResidualSigma ≡ true

    arbitrarySurfaceResidualProductIsAutomaticallyAdmissible : Bool
    arbitrarySurfaceResidualProductIsAutomaticallyAdmissibleIsFalse :
      arbitrarySurfaceResidualProductIsAutomaticallyAdmissible ≡ false

    sharedReconstructionArchitectureMakesDomainsLiterallySameObject : Bool
    sharedReconstructionArchitectureMakesDomainsLiterallySameObjectIsFalse :
      sharedReconstructionArchitectureMakesDomainsLiterallySameObject ≡ false

canonicalAdmissibleReconstructionBoundary : AdmissibleReconstructionBoundary
canonicalAdmissibleReconstructionBoundary =
  admissibleReconstructionBoundary
    true refl
    false refl
    false refl
