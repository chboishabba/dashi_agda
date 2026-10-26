module DASHI.Physics.QFT.NeutrinoHornedSU3RootExact where

------------------------------------------------------------------------
-- CP-NONZERO LEPTON RESIDUAL AS AN ACTUAL SU(3) MATRIX CANDIDATE.
--
-- THIS IS THE TARGET-SIDE CONSUMER OF THE HORNED GROUP'S NEW
-- POSITIVE COMPACT COMMUTATOR CONSTRUCTION (sibling PR #1244).
--
-- Original:
--   Morikuni Gotô, "A Theorem on compact semi-simple groups",
--   J Math Soc Japan 1 (1949), 270-272, DOI 10.2969/jmsj/00130270.
--   Hatcher, Algebraic Topology, Example 2B.2: free-group colimit.
--   C. Jarlskog, Phys Rev Lett 55 (1985), CP-odd invariants.
--
-- Reused existing DASHI:
--   NeutrinoExistingCPSectorLeptonBridgeExact.pmns
--   C3CyclotomicAmplitudeAlgebraExact, Q(zeta3) and conjugation
--   Monster3BCyclotomicLinearAlgebraExact, matrix scalar operations.
--
-- Actual target A=T*S1, T=diag(1,zeta,zeta²),
-- S1=U diag(1,-1,-1) U†=2 |u_1><u_1| - I.
-- All entries in exact Q(zeta3).  Prove A†A=I and det(A)=1
-- as nine exact finite rational cyclotomic equalities.
--
-- Mathematical consequence USING Gotô (not newly proved in Agda):
-- A is a single commutator in SU(3), every recursive child is also
-- a commutator; Hatcher tower yields a compatible G_A→SU(3)
-- representation sending its chosen meridian to A.
-- Three arms conjugated by T yield C3-equivariant action of G⋊C3.
--
-- PHYSICAL NONPROMOTION: neither A nor its infinite-image horn
-- representation derives the PMNS phase, lepton Yukawas or dynamics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; normalize)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Empty using (⊥)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L
import DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact as N
import DASHI.Physics.QFT.NeutrinoExistingCPSectorLeptonBridgeExact as CP

open N using (Flavour; electron; muon; tau; MassBasis; mass1)

phaseT : Flavour → C.Cyclotomic3
phaseT electron = C.one
phaseT muon = C.zeta
phaseT tau = C.zetaSquared

kronecker : Flavour → Flavour → C.Cyclotomic3
kronecker electron electron = C.one
kronecker muon muon = C.one
kronecker tau tau = C.one
kronecker _ _ = C.zero

two : ℚ
two = normalize 2 1

neutralResidualS1 : Flavour → Flavour → C.Cyclotomic3
neutralResidualS1 a b =
  L.add
    (L.scale two (C.multiply
      (CP.pmns a mass1) (C.conjugate (CP.pmns b mass1))))
    (L.negate (kronecker a b))

selectedTS : Flavour → Flavour → C.Cyclotomic3
selectedTS a b = C.multiply (phaseT a) (neutralResidualS1 a b)

adjointTS : Flavour → Flavour → C.Cyclotomic3
adjointTS a b = C.conjugate (selectedTS b a)

sum3 : C.Cyclotomic3 → C.Cyclotomic3 → C.Cyclotomic3 →
  C.Cyclotomic3
sum3 x y z = L.add x (L.add y z)

productMatrix :
  (Flavour → Flavour → C.Cyclotomic3) →
  (Flavour → Flavour → C.Cyclotomic3) →
  Flavour → Flavour → C.Cyclotomic3
productMatrix A B a b =
  sum3
    (C.multiply (A a electron) (B electron b))
    (C.multiply (A a muon) (B muon b))
    (C.multiply (A a tau) (B tau b))

selectedTSUnitaryRight : (a b : Flavour) →
  productMatrix selectedTS adjointTS a b ≡ kronecker a b
selectedTSUnitaryRight electron electron = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryRight electron muon = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryRight electron tau = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryRight muon electron = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryRight muon muon = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryRight muon tau = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryRight tau electron = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryRight tau muon = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryRight tau tau = C.cyclotomic3Ext (solve []) (solve [])

selectedTSUnitaryLeft : (a b : Flavour) →
  productMatrix adjointTS selectedTS a b ≡ kronecker a b
selectedTSUnitaryLeft electron electron = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryLeft electron muon = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryLeft electron tau = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryLeft muon electron = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryLeft muon muon = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryLeft muon tau = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryLeft tau electron = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryLeft tau muon = C.cyclotomic3Ext (solve []) (solve [])
selectedTSUnitaryLeft tau tau = C.cyclotomic3Ext (solve []) (solve [])

determinant3 :
  (Flavour → Flavour → C.Cyclotomic3) → C.Cyclotomic3
determinant3 M =
  L.add
    (L.add
      (L.add
        (C.multiply (M electron electron)
          (C.multiply (M muon muon) (M tau tau)))
        (C.multiply (M electron muon)
          (C.multiply (M muon tau) (M tau electron))))
      (C.multiply (M electron tau)
        (C.multiply (M muon electron) (M tau muon))))
    (L.negate
      (L.add
        (L.add
          (C.multiply (M electron tau)
            (C.multiply (M muon muon) (M tau electron)))
          (C.multiply (M electron muon)
            (C.multiply (M muon electron) (M tau tau))))
        (C.multiply (M electron electron)
          (C.multiply (M muon tau) (M tau muon)))))

selectedTSDeterminantOne :
  determinant3 selectedTS ≡ C.one
selectedTSDeterminantOne =
  C.cyclotomic3Ext (solve []) (solve [])

------------------------------------------------------------------------
-- Direct discharge of the NEW compact-Lie inner-C3 prerequisite.
-- T is a real SU(3) diagonal matrix over the existing Q(zeta3)
-- exact amplitude carrier, not an extra order-three automorphism
-- assumed independently. Its literal cube has 9 entries of I.
-- These entries become the group-valued T³=I after the certified
-- Q(zeta3) 3x3 matrix-realization equality is supplied.
------------------------------------------------------------------------

chargedRotationT : Flavour → Flavour → C.Cyclotomic3
chargedRotationT a b = C.multiply (phaseT a) (kronecker a b)

chargedRotationTAdjoint : Flavour → Flavour → C.Cyclotomic3
chargedRotationTAdjoint a b = C.conjugate (chargedRotationT b a)

chargedRotationCubeIsIdentity :
  (a b : Flavour) →
  productMatrix chargedRotationT
    (productMatrix chargedRotationT chargedRotationT) a b
    ≡ kronecker a b
chargedRotationCubeIsIdentity electron electron = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationCubeIsIdentity electron muon = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationCubeIsIdentity electron tau = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationCubeIsIdentity muon electron = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationCubeIsIdentity muon muon = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationCubeIsIdentity muon tau = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationCubeIsIdentity tau electron = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationCubeIsIdentity tau muon = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationCubeIsIdentity tau tau = C.cyclotomic3Ext (solve []) (solve [])

chargedRotationSpecialDeterminant :
  determinant3 chargedRotationT ≡ C.one
chargedRotationSpecialDeterminant =
  C.cyclotomic3Ext (solve []) (solve [])

chargedRotationUnitaryRight :
  (a b : Flavour) →
  productMatrix chargedRotationT chargedRotationTAdjoint a b
    ≡ kronecker a b
chargedRotationUnitaryRight electron electron = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationUnitaryRight electron muon = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationUnitaryRight electron tau = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationUnitaryRight muon electron = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationUnitaryRight muon muon = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationUnitaryRight muon tau = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationUnitaryRight tau electron = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationUnitaryRight tau muon = C.cyclotomic3Ext (solve []) (solve [])
chargedRotationUnitaryRight tau tau = C.cyclotomic3Ext (solve []) (solve [])

chargedRotationUnitaryLeft :
  (a b : Flavour) →
  productMatrix chargedRotationTAdjoint chargedRotationT a b
    ≡ kronecker a b
chargedRotationUnitaryLeft electron electron = C.cyclotomic3Ext (solve []) (solve [])

chargedRotationUnitaryLeft electron muon = C.cyclotomic3Ext (solve []) (solve [])

chargedRotationUnitaryLeft electron tau = C.cyclotomic3Ext (solve []) (solve [])

chargedRotationUnitaryLeft muon electron = C.cyclotomic3Ext (solve []) (solve [])

chargedRotationUnitaryLeft muon muon = C.cyclotomic3Ext (solve []) (solve [])

chargedRotationUnitaryLeft muon tau = C.cyclotomic3Ext (solve []) (solve [])

chargedRotationUnitaryLeft tau electron = C.cyclotomic3Ext (solve []) (solve [])

chargedRotationUnitaryLeft tau muon = C.cyclotomic3Ext (solve []) (solve [])

chargedRotationUnitaryLeft tau tau = C.cyclotomic3Ext (solve []) (solve [])

------------------------------------------------------------------------
-- The threefold symmetry is ACTUALLY NONTRIVIAL on our selected CP
-- root, not merely an abstract automorphism with cube identity.
-- Ad_T(A)_eμ differs from A_eμ by the exact (1,zeta) coefficient
-- pair (7429123333440,2394922626720)/6270551970029.
-- Original Jarlskog/CP physics is not implied by this group orbit.
------------------------------------------------------------------------

rotateByChargedT :
  (Flavour → Flavour → C.Cyclotomic3) →
  Flavour → Flavour → C.Cyclotomic3
rotateByChargedT M =
  productMatrix chargedRotationT
    (productMatrix M chargedRotationTAdjoint)

rotationDifferenceElectronMuon : C.Cyclotomic3
rotationDifferenceElectronMuon =
  L.add
    (rotateByChargedT selectedTS electron muon)
    (L.negate (selectedTS electron muon))

rotationDifferenceRationalExact :
  C.rationalCoeff rotationDifferenceElectronMuon
    ≡ normalize 7429123333440 6270551970029
rotationDifferenceRationalExact = solve []

rotationDifferenceZetaExact :
  C.zetaCoeff rotationDifferenceElectronMuon
    ≡ normalize 2394922626720 6270551970029
rotationDifferenceZetaExact = solve []

chargedRotationActuallyMovesCPRoot :
  rotateByChargedT selectedTS electron muon
    ≡ selectedTS electron muon → ⊥
chargedRotationActuallyMovesCPRoot ()

-- Original analytic determinant-one complex embedding of Q(zeta3)
-- maps this algebraic unitarity result into the usual SU(3).
-- Complete complex analytic embedding is a separate existing
-- physical and kernel-boundary obligation.

-- Noninteger trace and exact fifth-power obstruction are distinct
-- already source-written in:
-- NeutrinoExistingCPFiniteResidualNoGoExact, and
-- NeutrinoHornedExteriorFifthPowerNoGoExact.
-- A^5!=I has an independent exact-Fraction computation and is
-- not reasserted by a tautological proof about the A_ee entry.
