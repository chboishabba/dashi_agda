{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.UnificationUCT4ToModuloNullLinearityExact where

------------------------------------------------------------------------
-- PAPER 8 / UCT.4 -> UCT.5 TYPED TRANSPORT
--
-- UCT.4 gives nullity of the exact gluing cross-term.  To obtain true
-- modulo-null additivity of G one still needs quotient semantics:
--
--   nullClass x -> moduloNullEqual x zeroV
--   representative invariance
--   algebraic transport from zero cross-term to G(s1+s2)=Gs1+Gs2 modulo null.
--
-- This module makes those proof obligations explicit and derives UCT.5 once
-- they are supplied.  It does not manufacture quotient semantics.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.GluingOperatorLinearityOnDefectQuotientBoundary as U1a
import DASHI.Physics.Closure.UnificationCrossTermNullityTheoremBoundary as Boundary
import DASHI.Physics.Closure.UnificationUCTFullProofSpineExact as UCT

record UCT4ToModuloNullPackage
    {V : U1a.AdmissibleDefectQuotientVBoundary}
    {G-boundary : U1a.GluingOperatorGBoundary V}
    (uct : UCT.UCTAnalyticPackage V G-boundary) : Setω where
  field
    moduloNullEqual :
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V →
      Set

    representativeEquivalent :
      U1a.DefectQuotientV V →
      U1a.DefectQuotientV V →
      Set

    nullToZero :
      (x : U1a.DefectQuotientV V) →
      UCT.nullClass uct x →
      moduloNullEqual x (U1a.zeroV V)

    nullRepresentativeInvariant :
      (x y : U1a.DefectQuotientV V) →
      representativeEquivalent x y →
      UCT.nullClass uct x →
      UCT.nullClass uct y

    gluingRepresentativeInvariant :
      (x y : U1a.DefectQuotientV V) →
      representativeEquivalent x y →
      representativeEquivalent
        (U1a.G G-boundary x)
        (U1a.G G-boundary y)

    residualZeroImpliesModuloAdditivity :
      (s1 s2 : U1a.DefectQuotientV V) →
      moduloNullEqual
        (Boundary.actualU1aCrossTerm
          V G-boundary (UCT.-V_ uct) s1 s2)
        (U1a.zeroV V) →
      moduloNullEqual
        (U1a.G G-boundary (U1a._+V_ V s1 s2))
        (U1a._+V_ V
          (U1a.G G-boundary s1)
          (U1a.G G-boundary s2))

open UCT4ToModuloNullPackage public

uct4CrossTermIsZeroModuloNull :
  ∀ {V G-boundary}
    {uct : UCT.UCTAnalyticPackage V G-boundary} →
  (transport : UCT4ToModuloNullPackage uct) →
  (s1 s2 : U1a.DefectQuotientV V) →
  moduloNullEqual transport
    (Boundary.actualU1aCrossTerm
      V G-boundary (UCT.-V_ uct) s1 s2)
    (U1a.zeroV V)
uct4CrossTermIsZeroModuloNull {uct = uct} transport s1 s2 =
  nullToZero transport crossTerm
    (UCT.uct4CrossTermNullityTheorem uct s1 s2)
  where
    crossTerm =
      Boundary.actualU1aCrossTerm
        _ _ (UCT.-V_ uct) s1 s2

uct5ModuloNullAdditivity :
  ∀ {V G-boundary}
    {uct : UCT.UCTAnalyticPackage V G-boundary} →
  (transport : UCT4ToModuloNullPackage uct) →
  (s1 s2 : U1a.DefectQuotientV V) →
  moduloNullEqual transport
    (U1a.G G-boundary (U1a._+V_ V s1 s2))
    (U1a._+V_ V
      (U1a.G G-boundary s1)
      (U1a.G G-boundary s2))
uct5ModuloNullAdditivity transport s1 s2 =
  residualZeroImpliesModuloAdditivity transport s1 s2
    (uct4CrossTermIsZeroModuloNull transport s1 s2)

uct4ToUCT5CompilerLevel : ProofLevel
uct4ToUCT5CompilerLevel = machineChecked

nullToQuotientPhysicalLevel : ProofLevel
nullToQuotientPhysicalLevel = conditional

quotientRepresentativeInvariancePhysicalLevel : ProofLevel
quotientRepresentativeInvariancePhysicalLevel = conditional

residualToModuloAdditivityPhysicalLevel : ProofLevel
residualToModuloAdditivityPhysicalLevel = conditional
