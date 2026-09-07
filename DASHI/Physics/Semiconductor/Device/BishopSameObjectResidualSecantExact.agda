{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.BishopSameObjectResidualSecantExact where

------------------------------------------------------------------------
-- SAME-OBJECT ANALYTIC RESIDUAL SECANT
--
-- This owner derives the change of the actual Bishop two-cell continuity
-- residual between two admitted source states.  It does not reuse the old
-- finite 6,3,0 score.  The response is assembled from changes in the genuine
-- Bishop SG face fluxes plus changes in the currently modelled G/R terms.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell
import DASHI.Physics.Semiconductor.Device.FiniteScharfetterGummelFluxExact as Mesh
import DASHI.Physics.Semiconductor.Device.BishopSameObjectComputedFaceFluxExact as Flux
import DASHI.Physics.Semiconductor.Device.BishopTwoCellContinuityAssemblyExact as Assembly

signedDelta : BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ
signedDelta after before = BishopReal._-_ after before

electronFaceSecant :
  Cell.SourceCharge → Cell.SourceCharge → Mesh.SGFace → BishopReal.ℝ
electronFaceSecant before after face =
  signedDelta
    (Flux.bishopElectronFaceFlux after face)
    (Flux.bishopElectronFaceFlux before face)

holeFaceSecant :
  Cell.SourceCharge → Cell.SourceCharge → Mesh.SGFace → BishopReal.ℝ
holeFaceSecant before after face =
  signedDelta
    (Flux.bishopHoleFaceFlux after face)
    (Flux.bishopHoleFaceFlux before face)

generationASecant : Cell.SourceCharge → Cell.SourceCharge → BishopReal.ℝ
generationASecant before after =
  signedDelta (Assembly.generationA after) (Assembly.generationA before)

recombinationASecant : Cell.SourceCharge → Cell.SourceCharge → BishopReal.ℝ
recombinationASecant before after =
  signedDelta (Assembly.recombinationA after) (Assembly.recombinationA before)

generationBSecant : Cell.SourceCharge → Cell.SourceCharge → BishopReal.ℝ
generationBSecant before after =
  signedDelta (Assembly.generationB after) (Assembly.generationB before)

recombinationBSecant : Cell.SourceCharge → Cell.SourceCharge → BishopReal.ℝ
recombinationBSecant before after =
  signedDelta (Assembly.recombinationB after) (Assembly.recombinationB before)

------------------------------------------------------------------------
-- Sparse residual response assembled from face/source secants.
------------------------------------------------------------------------

electronResidualAResponse :
  Cell.SourceCharge → Cell.SourceCharge → BishopReal.ℝ
electronResidualAResponse before after =
  BishopReal._-_
    (BishopReal._+_
      (electronFaceSecant before after Mesh.face01)
      (generationASecant before after))
    (BishopReal._+_
      (electronFaceSecant before after Mesh.face12)
      (recombinationASecant before after))

holeResidualAResponse :
  Cell.SourceCharge → Cell.SourceCharge → BishopReal.ℝ
holeResidualAResponse before after =
  BishopReal._-_
    (BishopReal._+_
      (holeFaceSecant before after Mesh.face12)
      (recombinationASecant before after))
    (BishopReal._+_
      (holeFaceSecant before after Mesh.face01)
      (generationASecant before after))

electronResidualBResponse :
  Cell.SourceCharge → Cell.SourceCharge → BishopReal.ℝ
electronResidualBResponse before after =
  BishopReal._-_
    (BishopReal._+_
      (electronFaceSecant before after Mesh.face12)
      (generationBSecant before after))
    (BishopReal._+_
      (electronFaceSecant before after Mesh.face23)
      (recombinationBSecant before after))

holeResidualBResponse :
  Cell.SourceCharge → Cell.SourceCharge → BishopReal.ℝ
holeResidualBResponse before after =
  BishopReal._-_
    (BishopReal._+_
      (holeFaceSecant before after Mesh.face23)
      (recombinationBSecant before after))
    (BishopReal._+_
      (holeFaceSecant before after Mesh.face12)
      (generationBSecant before after))

------------------------------------------------------------------------
-- Exact secant identities for the actual analytic residual components.
------------------------------------------------------------------------

electronAResidualDifferenceExact :
  (before after : Cell.SourceCharge) →
  BishopReal._≃_
    (signedDelta
      (Assembly.electronResidualA after)
      (Assembly.electronResidualA before))
    (electronResidualAResponse before after)
electronAResidualDifferenceExact before after =
  let
    j01a = Flux.bishopElectronFaceFlux after Mesh.face01
    j01b = Flux.bishopElectronFaceFlux before Mesh.face01
    j12a = Flux.bishopElectronFaceFlux after Mesh.face12
    j12b = Flux.bishopElectronFaceFlux before Mesh.face12
    ga = Assembly.generationA after
    gb = Assembly.generationA before
    ra = Assembly.recombinationA after
    rb = Assembly.recombinationA before
    open BishopP.ℝ-Solver
  in
  solve 8
    (λ j01a′ j01b′ j12a′ j12b′ ga′ gb′ ra′ rb′ →
      (((j01a′ ⊕ ga′) ⊖ (j12a′ ⊕ ra′))
        ⊖ ((j01b′ ⊕ gb′) ⊖ (j12b′ ⊕ rb′)))
      ⊜ (((j01a′ ⊖ j01b′) ⊕ (ga′ ⊖ gb′))
        ⊖ ((j12a′ ⊖ j12b′) ⊕ (ra′ ⊖ rb′))))
    BishopP.≃-refl j01a j01b j12a j12b ga gb ra rb

holeAResidualDifferenceExact :
  (before after : Cell.SourceCharge) →
  BishopReal._≃_
    (signedDelta
      (Assembly.holeResidualA after)
      (Assembly.holeResidualA before))
    (holeResidualAResponse before after)
holeAResidualDifferenceExact before after =
  let
    j01a = Flux.bishopHoleFaceFlux after Mesh.face01
    j01b = Flux.bishopHoleFaceFlux before Mesh.face01
    j12a = Flux.bishopHoleFaceFlux after Mesh.face12
    j12b = Flux.bishopHoleFaceFlux before Mesh.face12
    ga = Assembly.generationA after
    gb = Assembly.generationA before
    ra = Assembly.recombinationA after
    rb = Assembly.recombinationA before
    open BishopP.ℝ-Solver
  in
  solve 8
    (λ j01a′ j01b′ j12a′ j12b′ ga′ gb′ ra′ rb′ →
      (((j12a′ ⊕ ra′) ⊖ (j01a′ ⊕ ga′))
        ⊖ ((j12b′ ⊕ rb′) ⊖ (j01b′ ⊕ gb′)))
      ⊜ (((j12a′ ⊖ j12b′) ⊕ (ra′ ⊖ rb′))
        ⊖ ((j01a′ ⊖ j01b′) ⊕ (ga′ ⊖ gb′))))
    BishopP.≃-refl j01a j01b j12a j12b ga gb ra rb

electronBResidualDifferenceExact :
  (before after : Cell.SourceCharge) →
  BishopReal._≃_
    (signedDelta
      (Assembly.electronResidualB after)
      (Assembly.electronResidualB before))
    (electronResidualBResponse before after)
electronBResidualDifferenceExact before after =
  let
    j12a = Flux.bishopElectronFaceFlux after Mesh.face12
    j12b = Flux.bishopElectronFaceFlux before Mesh.face12
    j23a = Flux.bishopElectronFaceFlux after Mesh.face23
    j23b = Flux.bishopElectronFaceFlux before Mesh.face23
    ga = Assembly.generationB after
    gb = Assembly.generationB before
    ra = Assembly.recombinationB after
    rb = Assembly.recombinationB before
    open BishopP.ℝ-Solver
  in
  solve 8
    (λ j12a′ j12b′ j23a′ j23b′ ga′ gb′ ra′ rb′ →
      (((j12a′ ⊕ ga′) ⊖ (j23a′ ⊕ ra′))
        ⊖ ((j12b′ ⊕ gb′) ⊖ (j23b′ ⊕ rb′)))
      ⊜ (((j12a′ ⊖ j12b′) ⊕ (ga′ ⊖ gb′))
        ⊖ ((j23a′ ⊖ j23b′) ⊕ (ra′ ⊖ rb′))))
    BishopP.≃-refl j12a j12b j23a j23b ga gb ra rb

holeBResidualDifferenceExact :
  (before after : Cell.SourceCharge) →
  BishopReal._≃_
    (signedDelta
      (Assembly.holeResidualB after)
      (Assembly.holeResidualB before))
    (holeResidualBResponse before after)
holeBResidualDifferenceExact before after =
  let
    j12a = Flux.bishopHoleFaceFlux after Mesh.face12
    j12b = Flux.bishopHoleFaceFlux before Mesh.face12
    j23a = Flux.bishopHoleFaceFlux after Mesh.face23
    j23b = Flux.bishopHoleFaceFlux before Mesh.face23
    ga = Assembly.generationB after
    gb = Assembly.generationB before
    ra = Assembly.recombinationB after
    rb = Assembly.recombinationB before
    open BishopP.ℝ-Solver
  in
  solve 8
    (λ j12a′ j12b′ j23a′ j23b′ ga′ gb′ ra′ rb′ →
      (((j23a′ ⊕ ra′) ⊖ (j12a′ ⊕ ga′))
        ⊖ ((j23b′ ⊕ rb′) ⊖ (j12b′ ⊕ gb′)))
      ⊜ (((j23a′ ⊖ j23b′) ⊕ (ra′ ⊖ rb′))
        ⊖ ((j12a′ ⊖ j12b′) ⊕ (ga′ ⊖ gb′))))
    BishopP.≃-refl j12a j12b j23a j23b ga gb ra rb

------------------------------------------------------------------------
-- The two historical adjacent source moves are now named analytic secants,
-- without importing their old finite residual magnitudes.
------------------------------------------------------------------------

data AdmittedSourceSecant : Set where
  q1ToQ3 q3ToQ5 : AdmittedSourceSecant

secantBefore : AdmittedSourceSecant → Cell.SourceCharge
secantBefore q1ToQ3 = Cell.q1
secantBefore q3ToQ5 = Cell.q3

secantAfter : AdmittedSourceSecant → Cell.SourceCharge
secantAfter q1ToQ3 = Cell.q3
secantAfter q3ToQ5 = Cell.q5

record AnalyticResidualSecant (move : AdmittedSourceSecant) : Set where
  constructor analyticResidualSecant
  field
    electronAResponse : BishopReal.ℝ
    holeAResponse : BishopReal.ℝ
    electronBResponse : BishopReal.ℝ
    holeBResponse : BishopReal.ℝ

open AnalyticResidualSecant public

computedAnalyticResidualSecant :
  (move : AdmittedSourceSecant) → AnalyticResidualSecant move
computedAnalyticResidualSecant move = analyticResidualSecant
  (electronResidualAResponse (secantBefore move) (secantAfter move))
  (holeResidualAResponse (secantBefore move) (secantAfter move))
  (electronResidualBResponse (secantBefore move) (secantAfter move))
  (holeResidualBResponse (secantBefore move) (secantAfter move))

------------------------------------------------------------------------
-- Remaining inversion boundary.
------------------------------------------------------------------------

data AnalyticSecantResidualLeaf : Set where
  ResidualNormOrOrdering : AnalyticSecantResidualLeaf
  SecantNonsingularity : AnalyticSecantResidualLeaf
  InverseSecantAction : AnalyticSecantResidualLeaf
  DampingOrLineSearch : AnalyticSecantResidualLeaf
  BasinPreservation : AnalyticSecantResidualLeaf

-- Same-object analytic residual secant != inverse response.  This owner derives
-- what changed; it does not yet claim that the response is invertible or that
-- either admitted source move is Newton-optimal.
