# Physical developmental operators — Round 20

Round 20 turns the existing origin-of-life / agentic-material / morphogenesis ladder into a physical adapter layer over existing DASHI owners.

The central object is no longer an untyped arrow `matter -> life -> brain`.  It is a factorized state evolution with explicit physical carriers, balance laws, consumer projections, and source boundaries.

## Imported owners

This tranche reuses rather than replaces:

- `DASHI.Physics.Units.SI` for type-indexed SI dimensions and fixed-point quantities;
- `DASHI.Physics.Laws.ThermodynamicStatisticalLaws` for thermodynamic, nonequilibrium, ensemble and stochastic authority boundaries;
- `DASHI.Physics.Laws.ContinuumMaterialLaws` for continuum balances, constitutive closures and reaction-diffusion surfaces;
- `DASHI.Biology.Morphogenesis.ReactionDiffusionHodgeBridge` / `ReactionDiffusionModeSelection` for existing finite Turing/Hodge structure;
- `DASHI.Biology.Cell.BioelectricNetwork` for coupled cell/tissue voltage-current-channel-gap-junction dynamics;
- `DASHI.Biology.Levin.BioelectricChemistryWaveAdapter` and `AgenticMaterialsControlCore` for chemistry/wave and agency boundaries;
- `DASHI.Biology.DNACompiledOperatorsRegression` for existing DNA carrier/codec operators;
- the Round-19 future-quotient machinery for consumer-relative dynamic safety.

## SI biological dimensions

`SIBiologyDimensionsExact` adds dimensions needed by the physical biology lane without modifying the SI owner:

- molar flux: `mol m^-2 s^-1`;
- diffusivity: `m^2 s^-1`;
- molar reaction rate: `mol m^-3 s^-1`;
- molar flow: `mol s^-1`;
- surface tension: `N m^-1`;
- force density: `N m^-3`;
- current density: `A m^-2`;
- capacitance per area;
- entropy-flow rate: `J K^-1 s^-1`.

The point is compile-time dimensional separation, not empirical calibration.

## Conservative reaction-diffusion regression

`FiniteReactionDiffusionConservationExact` defines a two-compartment transport state `(l,r)`.  One directed diffusion quantum implements

`(suc l,r) -> (l,suc r)`

and proves exact material conservation.  A source operator then gives the discrete balance

`total(step(q,x)) = q + total(x)`.

The continuum signature is tied to SI concentration, molar flux, diffusivity and reaction-rate carriers.

Primary source: Alan M. Turing, *The Chemical Basis of Morphogenesis* (1952), DOI `10.1098/rstb.1952.0012`.

## Chemical affinity and nonequilibrium throughput

`ChemicalAffinityEntropyProductionExact` separates forward free-energy affinity from reaction throughput.  In the finite nonnegative regression,

`affinity = reactantPotential - productPotential`

(truncated only because the carrier is `Nat`) and

`dissipatedPower = molarFlow * affinity`.

The canonical regression is `7 - 3 = 4` and `2 * 4 = 8`; zero affinity gives zero dissipative power.  SI carrier types separate molar energy, molar flow, power and entropy-flow rate.

Primary source: Jeremy L. England, *Statistical physics of self-replication* (2013), DOI `10.1063/1.4818538`.

No logarithmic chemical-potential law or England stochastic heat lower bound is claimed by the finite arithmetic.

## Compartmentalisation

`CompartmentMembraneTransportExact` makes the proto-cell boundary physical.  A one-quantum inward permeation move conserves total solute exactly.  The membrane signature includes area, volume, permeability, transmembrane voltage, surface tension, osmotic pressure, concentration and electrochemical potential.

Primary source: Peter Mitchell, *Coupling of Phosphorylation to Electron and Hydrogen Transfer by a Chemi-Osmotic type of Mechanism* (1961), DOI `10.1038/191144a0`.

## Bioelectric / metabolic coupling

`ElectrochemicalMembranePowerExact` gives exact finite arithmetic for

`I = g * dV`

and

`P_metabolic = J_ATP * dG_ATP`.

Its canonical witness has electrical demand `8` and metabolic supply `12`, with a proof that demand lies within supply.  The SI signature uses voltage, conductance, current, molar flow, molar free energy and power.

Source-facing mechanisms:

- A. L. Hodgkin and A. F. Huxley, *A quantitative description of membrane current and its application to conduction and excitation in nerve* (1952), DOI `10.1113/jphysiol.1952.sp004764`;
- Peter Mitchell (1961), DOI `10.1038/191144a0`;
- Michael Levin, *Bioelectric signaling: Reprogrammable circuits underlying embryogenesis, regeneration, and cancer* (2021), DOI `10.1016/j.cell.2021.02.034`.

`SIBioelectricNetworkAdapterExact` then instantiates the existing abstract `BioelectricNetwork` with SI-indexed millivolt voltage, nanosiemens conductance and nanoampere current carriers.

## Mechanochemical morphogenesis and positional information

`MechanochemicalMorphogenesisSIExact` supplies SI carriers for mass density, velocity, stress, force density and strain while leaving constitutive mechanics in `ContinuumMaterialLaws`.

Its finite spatial regression keeps organ identity fixed while changing a two-site morphogen field.  The field changes the decoded anchor, proving a concrete distinction between `hand` and `hand-here`.

## Goal factorization

`DevelopmentalGoalFactorizationExact` makes the target compositional:

`Goal = organ × anchor × owner × side × scale`.

It proves:

- the same generic `hand` can have distinct anchors;
- the same `hand-here` can have distinct owners;
- therefore generic organ identity does not reconstruct `hand-here`, and `hand-here` does not reconstruct `our-hand`.

A finite developmental operator factors genome/context through regulatory, bioelectric and mechanical stages.  Same genome plus different epigenetic context can produce different morphology.

## Dynamic safety

`DevelopmentalHiddenStateFutureDefectExact` instantiates the repository's proof-bearing dynamical quotient machinery.  Two fine states have identical present morphology but different hidden control state; under the same admissible developmental action their future morphologies differ.  Hence morphology-only projection cannot satisfy dynamic consumer safety.

This is a concrete biological example of the PNF invariant: present observational equality does not license forgetting a hidden physical state that changes future developmental behavior.

## p-adic carrier boundary

`PadicPhysicalParameterProjectionExact` uses the existing p-adic cylinder carrier.  Two depth-two states share the same depth-one prefix but have different retained fine digits, and the fine digit selects different downstream parameter values.  This proves that p-adic truncation is an information projection; it does **not** assert that physical chemistry is intrinsically p-adic.

## Origins-of-life stage separation

`PhysicalOriginsLadderExact` refines the existing `AgenticMaterialsControlCore` stages with an explicit capability signature.  It proves that self-amplification can appear before target-relative corrective feedback, while closed-loop proto-agency has corrective feedback.  A finite replicator doubles 1 -> 2 -> 4 -> 8, independently of a finite corrective controller that maps `damaged -> target` and fixes `target`.

Primary sources:

- Jeremy L. England (2013), DOI `10.1063/1.4818538`;
- Sumantra Sarkar and Jeremy L. England, *Design of conditions for self-replication* (2019), DOI `10.1103/PhysRevE.100.022414`.

## Cell / brain operator bridge

`CellBrainTransducerBridgeExact` proves a structural fact already implicit in the repository: any `BioelectricNetwork` update can be wrapped as a `StatefulTransducer`

`chemical input × prior network state × (environment, mechanics, regulation) -> network output × successor state`.

This does not identify brains with generic tissues.  It places specialized neural cellular networks and non-neural cellular collectives in a common stateful-network operator class.

## Integrated developmental step

`PhysicalDevelopmentalOperatorSystemExact` composes a finite state with chemical inventory, epigenetic/regulatory/electrical/metabolic/mechanical/morphological coordinates and a compositional target goal.  Its update is explicitly factorized into source, regulatory, electrical, mechanical and morphology operators.  It proves that the chemical source balance survives the downstream operators and imports the morphology-only future-safety failure.

The cumulative owner bundle carries actual theorem-bearing SI, reaction-diffusion, membrane, mechanics, origins and transducer owners rather than a list of Boolean completion receipts.

## Boundary

Round 20 does **not** claim:

- a calibrated molecular model of abiogenesis;
- England's full stochastic thermodynamic inequality;
- a complete Hodgkin-Huxley cell model;
- a complete mechanochemical hand-development model;
- that p-adic coordinates are literal physical spacetime;
- that morphology or voltage alone is a universal morphogenetic code;
- that brains and non-neural tissues have identical mechanisms.

It does close the structural gap identified in the attached roadmap: the origin/development ladder now has SI carrier types, exact finite conservation/balance regressions, explicit developmental factorization, and a consumer-relative future-safety theorem connected to the existing physical-law owners.
