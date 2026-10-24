module DASHI.Mathematics.Topology.ExoticCWExistingDonorWeldExact where

------------------------------------------------------------------------
-- CW prior-art reuse. J. H. C. Whitehead (classical CW theory);
-- Eilenberg--Steenrod (cochains). NO claim that Whitehead's theorem
-- or a universal CW topological realisation is proved here.
--
-- Existing actual contributors:
--  DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineCellularH2Exact
--  DASHI.Mathematics.Topology.FiniteCochainComplexExact
--
-- The first already computes the rational cellular H² model for
-- the standard 0/2-cell sphere presentation; the second already
-- supplies the abstract 3-term cochain laws. THIS file simply
-- instantiates and welds those TWO existing implementations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Mathematics.Topology.FiniteCochainComplexExact as Cochain
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineCellularH2Exact as CP1
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineCycleClassExact as Cycle

-- C^0=Q, C^1=0 represented by Unit, C^2=Q;
-- both differentials vanish. The 0-cochain and 2-cochain
-- representations are the existing donors, not duplicated.
cp1CellularThreeTerm : Cochain.ThreeTermCochainComplex
cp1CellularThreeTerm = record
  { C0 = ℚ
  ; C1 = ⊤
  ; C2 = CP1.CP1CellularDegreeTwoCochain
  ; zero2 = CP1.cellularZero
  ; d0 = λ _ → tt
  ; d1 = CP1.degreeOneCoboundary
  ; dSquaredZero = λ _ → refl
  }

cp1DegreeOneIsClosed : Cochain.Closed1 cp1CellularThreeTerm tt
cp1DegreeOneIsClosed = refl

cp1DegreeOneIsExact : Cochain.Exact1 cp1CellularThreeTerm tt
cp1DegreeOneIsExact = 0ℚ , refl

cp1CochainIdentity :
  Cochain.CochainMap cp1CellularThreeTerm cp1CellularThreeTerm
cp1CochainIdentity = Cochain.identityCochainMap cp1CellularThreeTerm

cp1IdentityPreservesClosed :
  Cochain.Closed1 cp1CellularThreeTerm
    (Cochain.map1 cp1CochainIdentity tt)
cp1IdentityPreservesClosed =
  Cochain.cochainMapPreservesClosed
    cp1CochainIdentity tt cp1DegreeOneIsClosed

cp1IdentityPreservesExact :
  Cochain.Exact1 cp1CellularThreeTerm
    (Cochain.map1 cp1CochainIdentity tt)
cp1IdentityPreservesExact =
  Cochain.cochainMapPreservesExact
    cp1CochainIdentity tt cp1DegreeOneIsExact

-- The original CP1 proof, not a new unverified quotient construction,
-- already gives rational H² <-> degree-two cochain data.
cp1H2RoundTripLeft : (cochain : CP1.CP1CellularDegreeTwoCochain) →
  CP1.h2ToCochain (CP1.cochainToH2 cochain) ≡ cochain
cp1H2RoundTripLeft = CP1.cochainH2LeftInverse

cp1H2RoundTripRight : (value : CP1.CP1CellularH2) →
  CP1.cochainToH2 (CP1.h2ToCochain value) ≡ value
cp1H2RoundTripRight = CP1.cochainH2RightInverse

-- The original P1 cycle-class-to-H² identification is inherited.
cp1PointIsCellularGenerator :
  CP1.p1H11ToCellularH2
    (Cycle.p1CycleClass
      Cycle.pointCycle)
    ≡ CP1.cellularPointGenerator
cp1PointIsCellularGenerator = CP1.pointCycleClassWeldsToCellularGenerator
