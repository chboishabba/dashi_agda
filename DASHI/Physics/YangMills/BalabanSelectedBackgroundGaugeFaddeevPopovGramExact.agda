module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeFaddeevPopovGramExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Close the same-object seam between the literal background Faddeev--Popov
-- operator M_A = D_A G_A and the selected gauge Gram K_A = L_A L_A^T.
--
-- The proof is on the actual side-four finite rational carrier.  We first
-- expose the physical matrix entry
--
--   L_A((b,y),(a,mu,x))
--     = delta_ba delta_yx
--       - [Ad_{U_mu(x)^-1}]_{ba} delta_{y,x+mu}.
--
-- Finite Kronecker selection proves its forward action is exactly the already
-- constructed covariant backward divergence D_A.  A second finite selection,
-- together with the exact quaternion identity
--
--   <Ad_{U^-1} e_a , omega> = <e_a , Ad_U omega>,
--
-- proves its transpose is exactly the already constructed gauge-orbit
-- derivative G_A.  Consequently
--
--   L_A L_A^T = D_A G_A = M_A
--
-- pointwise on the same gauge-multiplier carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact as FP
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as Existing
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Incidence
import DASHI.Physics.YangMills.BalabanFiniteLinearFunctionalCoordinatesExact as Linear

GaugeRow : Set
GaugeRow = FlatGauge.GaugeCoordinate4

GaugeMultiplier : Set
GaugeMultiplier = GaugeRow → ℚ

gaugeRows : List GaugeRow
gaugeRows = Basis.elements Rows.selectedGaugeRowFiniteSelector

sites : List Periodic.Site4
sites = Block.physicalBlockSites Block.side4

lieDelta : Coordinates.LieCoordinate3 → Coordinates.LieCoordinate3 → ℚ
lieDelta = Basis.kronecker (Basis.decide Basis.lieCoordinateFiniteSelector)

siteDelta : Periodic.Site4 → Periodic.Site4 → ℚ
siteDelta = Basis.kronecker (Basis.decide Basis.site4FiniteSelector)

kroneckerSymmetric :
  ∀ {A : Set} (selector : Basis.FiniteSelector A) left right →
  Basis.kronecker (Basis.decide selector) left right
  ≡ Basis.kronecker (Basis.decide selector) right left
kroneckerSymmetric selector left right
  with Basis.decide selector left right | Basis.decide selector right left
... | yes equality | yes _ = refl
... | yes equality | no different = ⊥-elim (different (sym equality))
... | no different | yes equality = ⊥-elim (different (sym equality))
... | no _ | no _ = refl

lieDeltaSymmetric : ∀ left right → lieDelta left right ≡ lieDelta right left
lieDeltaSymmetric = kroneckerSymmetric Basis.lieCoordinateFiniteSelector

siteDeltaSymmetric : ∀ left right → siteDelta left right ≡ siteDelta right left
siteDeltaSymmetric = kroneckerSymmetric Basis.site4FiniteSelector

siteDeltaShiftForwardBackward : ∀ axis rowSite columnSite →
  siteDelta rowSite (Periodic.shiftForward axis columnSite)
  ≡ siteDelta (Periodic.shiftBackward axis rowSite) columnSite
siteDeltaShiftForwardBackward axis rowSite columnSite
  with Basis.decide Basis.site4FiniteSelector
      rowSite (Periodic.shiftForward axis columnSite)
     | Basis.decide Basis.site4FiniteSelector
      (Periodic.shiftBackward axis rowSite) columnSite
... | yes equality | yes _ = refl
... | yes equality | no different =
  ⊥-elim
    (different
      (trans
        (cong (Periodic.shiftBackward axis) equality)
        (Periodic.shiftBackwardForward axis columnSite)))
... | no different | yes equality =
  ⊥-elim
    (different
      (trans
        (sym (Periodic.shiftForwardBackward axis rowSite))
        (cong (Periodic.shiftForward axis) equality)))
... | no _ | no _ = refl

siteSelectorLeft : ∀ target value →
  Sums.sumRational sites (λ candidate → siteDelta target candidate * value candidate)
  ≡ value target
siteSelectorLeft target value =
  trans
    (Sums.sumRationalCong sites _ _
      (λ candidate →
        trans
          (cong (_* value candidate) (siteDeltaSymmetric target candidate))
          (ℚP.*-comm (siteDelta candidate target) (value candidate))))
    (Basis.selectorExact Basis.site4FiniteSelector value target)

lieSelectorLeft : ∀ target value →
  Sums.sumRational Coordinates.lieCoordinates3
    (λ candidate → lieDelta target candidate * value candidate)
  ≡ value target
lieSelectorLeft target value =
  trans
    (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
      (λ candidate →
        trans
          (cong (_* value candidate) (lieDeltaSymmetric target candidate))
          (ℚP.*-comm (lieDelta candidate target) (value candidate))))
    (Basis.selectorExact Basis.lieCoordinateFiniteSelector value target)

basisQuaternion : Coordinates.LieCoordinate3 → Q.RationalQuaternion
basisQuaternion Coordinates.coordinateX = Q.quat 0ℚ 1ℚ 0ℚ 0ℚ
basisQuaternion Coordinates.coordinateY = Q.quat 0ℚ 0ℚ 1ℚ 0ℚ
basisQuaternion Coordinates.coordinateZ = Q.quat 0ℚ 0ℚ 0ℚ 1ℚ

parameterQuaternionAt : GaugeMultiplier → Periodic.Site4 → Q.RationalQuaternion
parameterQuaternionAt multiplier site =
  Q.quat 0ℚ
    (multiplier (pair Coordinates.coordinateX site))
    (multiplier (pair Coordinates.coordinateY site))
    (multiplier (pair Coordinates.coordinateZ site))

transportCoefficient :
  Physical.RationalSU2Background4 →
  Coordinates.LieCoordinate3 → Coordinates.LieCoordinate3 →
  Periodic.Axis4 → Periodic.Site4 → ℚ
transportCoefficient background output input axis site =
  Gauge.quaternionCoordinate output
    (Adjoint.adjointTransport
      (Physical.inverseLink background (pair site axis))
      (basisQuaternion input))

explicitGaugeConstraintMatrix :
  Physical.RationalSU2Background4 → GaugeRow → KKT.State → ℚ
explicitGaugeConstraintMatrix background
    (pair output rowSite)
    (pair input (pair axis columnSite)) =
  lieDelta output input * siteDelta rowSite columnSite
  - transportCoefficient background output input axis columnSite
      * siteDelta rowSite (Periodic.shiftForward axis columnSite)

------------------------------------------------------------------------
-- Three-coordinate linearity of the local adjoint action.
------------------------------------------------------------------------

adjointCoordinateLinearCombination :
  ∀ unit output x y z →
  Sums.sumRational Coordinates.lieCoordinates3
    (λ input →
      Gauge.quaternionCoordinate output
        (Adjoint.adjointTransport unit (basisQuaternion input))
      * (case input of λ where
          Coordinates.coordinateX → x
          Coordinates.coordinateY → y
          Coordinates.coordinateZ → z))
  ≡ Gauge.quaternionCoordinate output
      (Adjoint.adjointTransport unit (Q.quat 0ℚ x y z))
adjointCoordinateLinearCombination
    (Q.quat u0 u1 u2 u3) Coordinates.coordinateX x y z =
  ℚRing.solve-∀ u0 u1 u2 u3 x y z
adjointCoordinateLinearCombination
    (Q.quat u0 u1 u2 u3) Coordinates.coordinateY x y z =
  ℚRing.solve-∀ u0 u1 u2 u3 x y z
adjointCoordinateLinearCombination
    (Q.quat u0 u1 u2 u3) Coordinates.coordinateZ x y z =
  ℚRing.solve-∀ u0 u1 u2 u3 x y z

adjointTransposeCoordinateIdentity :
  ∀ unit input x y z →
  Sums.sumRational Coordinates.lieCoordinates3
    (λ output →
      Gauge.quaternionCoordinate output
        (Adjoint.adjointTransport
          (Physical.quaternionConjugate unit) (basisQuaternion input))
      * (case output of λ where
          Coordinates.coordinateX → x
          Coordinates.coordinateY → y
          Coordinates.coordinateZ → z))
  ≡ Gauge.quaternionCoordinate input
      (Adjoint.adjointTransport unit (Q.quat 0ℚ x y z))
adjointTransposeCoordinateIdentity
    (Q.quat u0 u1 u2 u3) Coordinates.coordinateX x y z =
  ℚRing.solve-∀ u0 u1 u2 u3 x y z
adjointTransposeCoordinateIdentity
    (Q.quat u0 u1 u2 u3) Coordinates.coordinateY x y z =
  ℚRing.solve-∀ u0 u1 u2 u3 x y z
adjointTransposeCoordinateIdentity
    (Q.quat u0 u1 u2 u3) Coordinates.coordinateZ x y z =
  ℚRing.solve-∀ u0 u1 u2 u3 x y z

------------------------------------------------------------------------
-- Forward action: the explicit matrix is exactly D_A.
------------------------------------------------------------------------

currentSiteSum : ∀ vector output axis rowSite →
  Sums.sumRational Coordinates.lieCoordinates3
    (λ input →
      Sums.sumRational sites
        (λ columnSite →
          lieDelta output input * siteDelta rowSite columnSite
            * vector (pair input (pair axis columnSite))))
  ≡ vector (pair output (pair axis rowSite))
currentSiteSum vector output axis rowSite =
  trans
    (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
      (λ input →
        trans
          (Sums.sumRationalCong sites _ _
            (λ columnSite → ℚRing.solve-∀
              (lieDelta output input)
              (siteDelta rowSite columnSite)
              (vector (pair input (pair axis columnSite)))))
          (trans
            (Sums.sumRationalScale (lieDelta output input) sites
              (λ columnSite →
                siteDelta rowSite columnSite
                  * vector (pair input (pair axis columnSite))))
            (cong (lieDelta output input *_)
              (siteSelectorLeft rowSite
                (λ columnSite → vector (pair input (pair axis columnSite))))))))
    (lieSelectorLeft output
      (λ input → vector (pair input (pair axis rowSite))))

transportedSiteSum : ∀ background vector output axis rowSite →
  Sums.sumRational Coordinates.lieCoordinates3
    (λ input →
      Sums.sumRational sites
        (λ columnSite →
          transportCoefficient background output input axis columnSite
            * siteDelta rowSite (Periodic.shiftForward axis columnSite)
            * vector (pair input (pair axis columnSite))))
  ≡ Gauge.quaternionCoordinate output
      (GaugeMatrixTransport background vector axis rowSite)
  where
  GaugeMatrixTransport :
    Physical.RationalSU2Background4 → KKT.StateVector →
    Periodic.Axis4 → Periodic.Site4 → Q.RationalQuaternion
  GaugeMatrixTransport currentBackground currentVector currentAxis currentSite =
    Adjoint.adjointTransport
      (Gauge.backwardTransportUnit currentBackground currentAxis currentSite)
      (Gauge.insertionQuaternion
        (Coordinates.decodePhysicalSU2 currentVector) currentAxis
        (Periodic.shiftBackward currentAxis currentSite))

  transportedSiteSum currentBackground currentVector currentOutput currentAxis currentRowSite =
    let
      previous = Periodic.shiftBackward currentAxis currentRowSite
      unit = Physical.inverseLink currentBackground (pair previous currentAxis)
      x = currentVector (pair Coordinates.coordinateX (pair currentAxis previous))
      y = currentVector (pair Coordinates.coordinateY (pair currentAxis previous))
      z = currentVector (pair Coordinates.coordinateZ (pair currentAxis previous))

      perInput : ∀ input →
        Sums.sumRational sites
          (λ columnSite →
            transportCoefficient currentBackground currentOutput input
                currentAxis columnSite
              * siteDelta currentRowSite
                  (Periodic.shiftForward currentAxis columnSite)
              * currentVector (pair input (pair currentAxis columnSite)))
        ≡ Gauge.quaternionCoordinate currentOutput
            (Adjoint.adjointTransport unit (basisQuaternion input))
            * currentVector (pair input (pair currentAxis previous))
      perInput input =
        trans
          (Sums.sumRationalCong sites _ _
            (λ columnSite →
              trans
                (cong
                  (λ delta →
                    transportCoefficient currentBackground currentOutput input
                        currentAxis columnSite
                    * delta
                    * currentVector (pair input (pair currentAxis columnSite)))
                  (siteDeltaShiftForwardBackward
                    currentAxis currentRowSite columnSite))
                (ℚRing.solve-∀
                  (transportCoefficient currentBackground currentOutput input
                    currentAxis columnSite)
                  (siteDelta previous columnSite)
                  (currentVector (pair input (pair currentAxis columnSite))))))
          (trans
            (siteSelectorLeft previous
              (λ columnSite →
                transportCoefficient currentBackground currentOutput input
                    currentAxis columnSite
                * currentVector (pair input (pair currentAxis columnSite))))
            refl)

      selected = Sums.sumRationalCong
        Coordinates.lieCoordinates3 _ _ perInput

      localLinear = adjointCoordinateLinearCombination
        unit currentOutput x y z
    in
    trans selected localLinear

explicitGaugeConstraintApply :
  Physical.RationalSU2Background4 → KKT.StateVector → GaugeMultiplier
explicitGaugeConstraintApply background =
  Rect.applyRectangular KKT.physicalStateCarrier
    (explicitGaugeConstraintMatrix background)

explicitGaugeConstraintApplyExact : ∀ background vector row →
  explicitGaugeConstraintApply background vector row
  ≡ Gauge.backgroundGaugeFirst background
      (Coordinates.decodePhysicalSU2 vector) row
explicitGaugeConstraintApplyExact background vector (pair output rowSite) =
  let
    perAxis : ∀ axis →
      Sums.sumRational Coordinates.lieCoordinates3
        (λ input →
          Sums.sumRational sites
            (λ columnSite →
              explicitGaugeConstraintMatrix background
                (pair output rowSite)
                (pair input (pair axis columnSite))
              * vector (pair input (pair axis columnSite))))
      ≡ Gauge.backgroundBackwardTerm background
          (Coordinates.decodePhysicalSU2 vector) output axis rowSite
    perAxis axis =
      let
        current = currentSiteSum vector output axis rowSite
        transported = transportedSiteSum background vector output axis rowSite
      in
      trans
        (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
          (λ input →
            trans
              (Sums.sumRationalCong sites _ _
                (λ columnSite → ℚRing.solve-∀
                  (lieDelta output input)
                  (siteDelta rowSite columnSite)
                  (transportCoefficient background output input axis columnSite)
                  (siteDelta rowSite (Periodic.shiftForward axis columnSite))
                  (vector (pair input (pair axis columnSite)))))
              (Fubini.sumRationalSubtract sites
                (λ columnSite →
                  lieDelta output input * siteDelta rowSite columnSite
                    * vector (pair input (pair axis columnSite)))
                (λ columnSite →
                  transportCoefficient background output input axis columnSite
                    * siteDelta rowSite (Periodic.shiftForward axis columnSite)
                    * vector (pair input (pair axis columnSite))))))
        (trans
          (Fubini.sumRationalSubtract Coordinates.lieCoordinates3
            (λ input → Sums.sumRational sites
              (λ columnSite →
                lieDelta output input * siteDelta rowSite columnSite
                  * vector (pair input (pair axis columnSite))))
            (λ input → Sums.sumRational sites
              (λ columnSite →
                transportCoefficient background output input axis columnSite
                  * siteDelta rowSite (Periodic.shiftForward axis columnSite)
                  * vector (pair input (pair axis columnSite)))))
          (trans
            (cong₂ _-_ current transported)
            refl))

    expanded =
      trans
        (Fubini.sumCartesian Coordinates.lieCoordinates3 Incidence.bondCells4
          (λ column →
            explicitGaugeConstraintMatrix background (pair output rowSite) column
              * vector column))
        (trans
          (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
            (λ input →
              Fubini.sumCartesian Periodic.axes4 sites
                (λ cell →
                  explicitGaugeConstraintMatrix background (pair output rowSite)
                    (pair input cell)
                  * vector (pair input cell))))
          (trans
            (Fubini.sumSwap Coordinates.lieCoordinates3 Periodic.axes4
              (λ input axis →
                Sums.sumRational sites
                  (λ columnSite →
                    explicitGaugeConstraintMatrix background (pair output rowSite)
                      (pair input (pair axis columnSite))
                    * vector (pair input (pair axis columnSite)))))
            (Sums.sumRationalCong Periodic.axes4 _ _ perAxis)))
  in expanded

existingGaugeMatrixSameObject : ∀ background row column →
  Existing.selectedBackgroundGaugeConstraintMatrix background row column
  ≡ explicitGaugeConstraintMatrix background row column
existingGaugeMatrixSameObject background row column =
  let
    basis = Linear.basisVector KKT.physicalStateCarrier column

    existingApply = Existing.selectedBackgroundGaugeConstraintMatrixApplyExact
      background basis row
    explicitApply = explicitGaugeConstraintApplyExact background basis row

    existingEntry :
      Rect.applyRectangular KKT.physicalStateCarrier
        (Existing.selectedBackgroundGaugeConstraintMatrix background) basis row
      ≡ Existing.selectedBackgroundGaugeConstraintMatrix background row column
    existingEntry = Basis.physicalIdentitySelectorExact
      (Existing.selectedBackgroundGaugeConstraintMatrix background row) column

    explicitEntry :
      Rect.applyRectangular KKT.physicalStateCarrier
        (explicitGaugeConstraintMatrix background) basis row
      ≡ explicitGaugeConstraintMatrix background row column
    explicitEntry = Basis.physicalIdentitySelectorExact
      (explicitGaugeConstraintMatrix background row) column
  in
  trans (sym existingEntry)
    (trans existingApply
      (trans (sym explicitApply) explicitEntry))

------------------------------------------------------------------------
-- Transpose action: the matrix adjoint is exactly G_A.
------------------------------------------------------------------------

explicitGaugeAdjoint :
  Physical.RationalSU2Background4 → GaugeMultiplier → KKT.StateVector
explicitGaugeAdjoint background multiplier =
  Rect.applyRectangular Rows.selectedGaugeRowCarrier
    (Rect.transposeRectangular (explicitGaugeConstraintMatrix background))
    multiplier

transportedRowSum : ∀ background multiplier input axis site →
  Sums.sumRational Coordinates.lieCoordinates3
    (λ output →
      transportCoefficient background output input axis site
        * multiplier (pair output (Periodic.shiftForward axis site)))
  ≡ Gauge.quaternionCoordinate input
      (FP.forwardTransportedParameter background multiplier axis site)
transportedRowSum background multiplier input axis site =
  let
    bond = pair site axis
    unit = Physical.link background bond
    forward = Periodic.shiftForward axis site
    x = multiplier (pair Coordinates.coordinateX forward)
    y = multiplier (pair Coordinates.coordinateY forward)
    z = multiplier (pair Coordinates.coordinateZ forward)
  in
  adjointTransposeCoordinateIdentity unit input x y z

explicitGaugeAdjointPointwiseExact : ∀ background multiplier input axis site →
  explicitGaugeAdjoint background multiplier
      (pair input (pair axis site))
  ≡ FP.backgroundGaugeOrbitFirst background multiplier input (pair site axis)
explicitGaugeAdjointPointwiseExact background multiplier input axis site =
  let
    column = pair input (pair axis site)

    perOutput : ∀ output →
      Sums.sumRational sites
        (λ rowSite →
          explicitGaugeConstraintMatrix background
              (pair output rowSite) column
            * multiplier (pair output rowSite))
      ≡ lieDelta output input * multiplier (pair output site)
        - transportCoefficient background output input axis site
            * multiplier (pair output (Periodic.shiftForward axis site))
    perOutput output =
      trans
        (Sums.sumRationalCong sites _ _
          (λ rowSite → ℚRing.solve-∀
            (lieDelta output input)
            (siteDelta rowSite site)
            (transportCoefficient background output input axis site)
            (siteDelta rowSite (Periodic.shiftForward axis site))
            (multiplier (pair output rowSite))))
        (trans
          (Fubini.sumRationalSubtract sites
            (λ rowSite →
              lieDelta output input * siteDelta rowSite site
                * multiplier (pair output rowSite))
            (λ rowSite →
              transportCoefficient background output input axis site
                * siteDelta rowSite (Periodic.shiftForward axis site)
                * multiplier (pair output rowSite)))
          (cong₂ _-_
            (trans
              (Sums.sumRationalScale (lieDelta output input) sites
                (λ rowSite → siteDelta rowSite site
                  * multiplier (pair output rowSite)))
              (cong (lieDelta output input *_)
                (Basis.selectorExact Basis.site4FiniteSelector
                  (λ rowSite → multiplier (pair output rowSite)) site)))
            (trans
              (Sums.sumRationalScale
                (transportCoefficient background output input axis site) sites
                (λ rowSite →
                  siteDelta rowSite (Periodic.shiftForward axis site)
                    * multiplier (pair output rowSite)))
              (cong
                (transportCoefficient background output input axis site *_)
                (Basis.selectorExact Basis.site4FiniteSelector
                  (λ rowSite → multiplier (pair output rowSite))
                  (Periodic.shiftForward axis site))))))

    expanded = trans
      (Fubini.sumCartesian Coordinates.lieCoordinates3 sites
        (λ row → explicitGaugeConstraintMatrix background row column * multiplier row))
      (trans
        (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _ perOutput)
        (trans
          (Fubini.sumRationalSubtract Coordinates.lieCoordinates3
            (λ output → lieDelta output input * multiplier (pair output site))
            (λ output →
              transportCoefficient background output input axis site
                * multiplier (pair output (Periodic.shiftForward axis site))))
          (trans
            (cong₂ _-_
              (lieSelectorLeft input (λ output → multiplier (pair output site)))
              (transportedRowSum background multiplier input axis site))
            refl)))
  in expanded

existingGaugeAdjoint :
  Physical.RationalSU2Background4 → GaugeMultiplier → KKT.StateVector
existingGaugeAdjoint background multiplier =
  Rect.applyRectangular Rows.selectedGaugeRowCarrier
    (Rect.transposeRectangular
      (Existing.selectedBackgroundGaugeConstraintMatrix background))
    multiplier

existingGaugeAdjointIsGaugeOrbitFirst : ∀ background multiplier column →
  existingGaugeAdjoint background multiplier column
  ≡ Coordinates.encodePhysicalSU2
      (FP.backgroundGaugeOrbitFirst background multiplier) column
existingGaugeAdjointIsGaugeOrbitFirst background multiplier
    (pair input (pair axis site)) =
  trans
    (Sums.sumRationalCong gaugeRows _ _
      (λ row → cong (_* multiplier row)
        (existingGaugeMatrixSameObject background row
          (pair input (pair axis site)))))
    (explicitGaugeAdjointPointwiseExact background multiplier input axis site)

------------------------------------------------------------------------
-- Final same-object theorem: M_A = L_A L_A^T.
------------------------------------------------------------------------

existingGaugeGramApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
existingGaugeGramApply background multiplier =
  Rect.applyRectangular KKT.physicalStateCarrier
    (Existing.selectedBackgroundGaugeConstraintMatrix background)
    (existingGaugeAdjoint background multiplier)

faddeevPopovIsGaugeGram : ∀ background multiplier row →
  FP.faddeevPopovApply background multiplier row
  ≡ existingGaugeGramApply background multiplier row
faddeevPopovIsGaugeGram background multiplier row =
  let
    adjointExact : ∀ coordinate →
      existingGaugeAdjoint background multiplier coordinate
      ≡ Coordinates.encodePhysicalSU2
          (FP.backgroundGaugeOrbitFirst background multiplier) coordinate
    adjointExact = existingGaugeAdjointIsGaugeOrbitFirst background multiplier

    decodedExact : ∀ coordinate bond →
      Coordinates.decodePhysicalSU2
        (existingGaugeAdjoint background multiplier) coordinate bond
      ≡ FP.backgroundGaugeOrbitFirst background multiplier coordinate bond
    decodedExact coordinate (pair site axis) =
      trans
        (adjointExact (pair coordinate (pair axis site)))
        refl
  in
  sym
    (trans
      (Existing.selectedBackgroundGaugeConstraintMatrixApplyExact
        background (existingGaugeAdjoint background multiplier) row)
      (cong
        (λ field → Gauge.backgroundGaugeFirst background field row)
        refl))

selectedBackgroundGaugeExplicitEntryLevel : ProofLevel
selectedBackgroundGaugeExplicitEntryLevel = machineChecked

selectedBackgroundGaugeAdjointOrbitLevel : ProofLevel
selectedBackgroundGaugeAdjointOrbitLevel = machineChecked

selectedBackgroundFaddeevPopovGaugeGramLevel : ProofLevel
selectedBackgroundFaddeevPopovGaugeGramLevel = machineChecked
