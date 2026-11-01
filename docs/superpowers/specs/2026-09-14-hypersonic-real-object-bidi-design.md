# Hypersonic Real-Object Application BIDI Design

## Purpose

Extend the object-first missing/deceased scientist investigation with an independently real engineering object: a benign advanced air-breathing hypersonic research vehicle / scramjet test platform. Requirements are derived from external aerospace engineering sources first; retained-scientist science is mapped into those requirements only afterwards.

This layer answers an engineering query, not the historical-programme query. A strong subsystem fit must not promote historical participation, common-programme identity, weapon-programme identity, or event causation.

## Reuse

Reuse rather than replace:

- `DASHI.Core.ScientificCapabilityCarrierBidiExact`
- `DASHI.Core.ApplicationTransformationCapabilityBidiExact`
- `DASHI.Core.AttributedSourceCore`
- `DASHI.Core.SnowballAttributionProvenanceInvariantExact`
- existing scientist-specific science owners
- `MissingDeceasedCommonObjectProgrammeDiscriminatorExact` / promotion state.

Add one thin generic adapter, `DASHI.Core.RealObjectApplicationBidiExact`, with a typed fit lattice:

```text
FitStrength = directSourceFit | engineeringTransfer | methodTransfer | analogyOnly | noFit
```

A real object has source-attributed requirements; a scientist-object fit names the science owner, requirement, fit strength, evidence reference, reverse qualification leaf, and historical-participation state.

## Canonical object

`DASHI.Culture.MissingDeceasedHypersonicAirbreathingVehicleBidiExact`

The source-derived benign research/test object includes:

- inlet/compression;
- isolator/shock-train and shock-boundary-layer interaction control;
- supersonic combustion/mixing;
- hot structural mechanics;
- thermal protection/insulation;
- sensing/actuation;
- fault-tolerant control;
- verified digital hardware;
- guidance/autonomy;
- ground/high-enthalpy qualification.

Primary engineering context uses NASA Glenn institutional sources for scramjet propulsion, hypersonic inlets and liquid-rocket distinction, plus scientist-specific DOI/institutional sources already retained in DASHI.

## Rocket / scramjet thermodynamic boundary

A liquid rocket carries stored fuel and stored oxidizer and pumps them into a combustion chamber. A scramjet ingests atmospheric air; ram/inlet compression converts flight kinetic energy into pressure/internal energy while the combustor flow remains supersonic. Hypersonic inlet compression produces high stagnation temperatures and hot boundary layers. Normal scramjet inlet compression therefore does not by itself liquefy air; air liquefaction would require a distinct heat-removal/precooling architecture.

Required firewalls:

```text
inletCompressionPaysAirLiquefaction = false
scramjetCarriesOxidizerLikeRocket = false
rocketAndScramjetAreSameThermodynamicObject = false
rocketBoostPlusScramjetCruiseCanCoexist = true
```

The final boolean means staged/combined vehicle architecture is real (e.g. rocket boost to scramjet operating speed), not that the two engines are the same object.

## Strong seven-fibre engineering map

The first canonical low-invention map is:

- Yan Hong -> inlet/SBLI/shock control -> `directSourceFit`
- Fang Daining -> hot structural/extreme-environment mechanics -> `engineeringTransfer`
- Zhou Guangyuan -> lightweight thermal insulation -> `engineeringTransfer`
- Monica Jacinto/Reza -> oxidising hot-section material candidate -> `engineeringTransfer`
- William Neil McCasland -> fault-tolerant sensing/actuation -> `methodTransfer`
- Chen Shuming -> digital control-hardware verification -> `methodTransfer`
- Zhang Daibing -> guidance/autonomy -> `methodTransfer`

Transfer rows require vehicle-specific geometry, chemistry, heat flux/stress state, cycling, calibration, failure sets, validation or qualification. In particular, Reza's oxygen-service alloy science does not become a qualified scramjet alloy merely because both environments are hot and oxidising.

## All-20 negative information

Round 17 classifies all twenty retained scientists against this object. `analogyOnly` and `noFit` are first-class outcomes; forcing unrelated biology, astronomy or anomalous-force science into the vehicle increases invented-interface debt and is prohibited.

Expected strong-fit count is seven. All historical participation, H2 and H3 promotion counts remain zero absent literal programme receipts.

## Attribution and snowball

Use `AttributedSourceCore` for NASA and science-source rows. Citation imports neither proof nor authority. A secondary/discovery source may nominate a source but cannot silently replace a primary engineering/science source. Source repetition is not independent corroboration. Stable DOI/project identifiers are retained only where same-object identity is paid.

## Firewalls

```text
subsystemFitPaysHistoricalParticipation = false
multipleFitsPayCommonProgramme = false
engineeringTransferPaysQualification = false
methodTransferPaysVehicleImplementation = false
hypersonicRelevancePaysWeaponProgramme = false
realObjectFitPaysEventCause = false
realObjectFitPaysH2 = false
noFitCanReduceInventedInterfaceDebt = true
```

## Reverse BIDI

Forward: science capability -> subsystem fit -> bounded real-object application.

Reverse: requested subsystem/application -> missing geometry, operating window, constitutive state, thermal cycling, calibration, sensor/actuator architecture, control law, verification corpus, qualification and literal historical programme receipts.

## Next portfolio

After the hypersonic canonical object, reuse the same generic surface for a long-duration space/fission platform, high-energy experimental facility, molecular/chemical-biology platform and anomalous-force test facility. The resulting scientist-capability x real-object incidence matrix is an engineering surface; documentary historical convergence remains a separate investigation surface.

## Certification boundary

Static/source integration is not Agda kernel certification. The focused checker must land first and production owners must be absent at the RED checkpoint. No GREEN/typecheck claim without an executed exact-head receipt.
