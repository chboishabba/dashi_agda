module DASHI.Physics.Thermodynamics.CaloricRegenerator where

open import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial

------------------------------------------------------------------------
-- Porous solid/fluid regenerator interface.
--
-- No Darcy/Forchheimer coefficient, heat-transfer coefficient, geometry,
-- or discretisation is hard-coded here.  The point of this layer is to
-- own the coupling and conservation obligations while leaving calibrated
-- constitutive realisations downstream.
------------------------------------------------------------------------

record RegeneratorGeometry : Set₁ where
  field
    Position       : Set
    Porosity       : Set
    Permeability   : Set
    InterfaceArea  : Set
    FlowArea       : Set

    porosity       : Position → Porosity
    permeability   : Position → Permeability
    interfaceArea  : Position → InterfaceArea
    flowArea       : Position → FlowArea

record TransferMedium : Set₁ where
  field
    FluidState      : Set
    Temperature     : Set
    Pressure        : Set
    Density         : Set
    HeatCapacity    : Set
    Viscosity       : Set

    fluidTemperature : FluidState → Temperature
    pressure         : FluidState → Pressure
    density          : FluidState → Density
    heatCapacity     : FluidState → HeatCapacity
    viscosity        : FluidState → Viscosity

record CaloricRegenerator
  (M : MagnetocaloricMaterial)
  (G : RegeneratorGeometry)
  (F : TransferMedium) : Set₁ where
  field
    RegeneratorState  : Set
    SolidField        : Set
    FluidField        : Set
    FlowState         : Set
    HeatFlux          : Set
    PressureDrop      : Set

    solidField        : RegeneratorState → SolidField
    fluidField        : RegeneratorState → FluidField
    flowState         : RegeneratorState → FlowState
    heatFlux          : RegeneratorState → HeatFlux
    pressureDrop      : RegeneratorState → PressureDrop

    ForwardFlow       : FlowState → Set
    ReverseFlow       : FlowState → Set
    FlowReversal      : FlowState → FlowState → Set

record RegeneratorTransportLaw
  {M : MagnetocaloricMaterial}
  {G : RegeneratorGeometry}
  {F : TransferMedium}
  (R : CaloricRegenerator M G F) : Set₁ where
  open CaloricRegenerator R
  field
    SolidEnergyBalance  : RegeneratorState → Set
    FluidEnergyBalance  : RegeneratorState → Set
    InterfacialExchange : RegeneratorState → Set
    HydraulicLaw        : RegeneratorState → Set

    solidEnergyBalance  : (s : RegeneratorState) → SolidEnergyBalance s
    fluidEnergyBalance  : (s : RegeneratorState) → FluidEnergyBalance s
    interfacialExchange : (s : RegeneratorState) → InterfacialExchange s
    hydraulicLaw        : (s : RegeneratorState) → HydraulicLaw s

record RegeneratorAdmissibility
  {M : MagnetocaloricMaterial}
  {G : RegeneratorGeometry}
  {F : TransferMedium}
  (R : CaloricRegenerator M G F) : Set₁ where
  open CaloricRegenerator R
  field
    TransportConservative  : RegeneratorState → Set
    HydraulicallyAdmissible : RegeneratorState → Set
    ChannelsOpen            : RegeneratorState → Set

    transportConservative :
      (s : RegeneratorState) → TransportConservative s
    hydraulicallyAdmissible :
      (s : RegeneratorState) → HydraulicallyAdmissible s
    channelsOpen :
      (s : RegeneratorState) → ChannelsOpen s

record RegeneratorAuthorityBoundary : Set₁ where
  field
    porousGeometryRequiresMeasurement : Set
    hydraulicClosureRequiresCalibration : Set
    heatTransferCoefficientRequiresCalibration : Set
    conservationDoesNotImplyLowPressureDrop : Set
    reversibleFlowDoesNotImplyReversibleThermodynamics : Set
