#!/usr/bin/env python3
"""BR39–111 bounded local acceptance, no CI, no shell or OpenBLAS requirement.

Each original checker is a separate <=90-second subprocess. Receipt identity
includes *source digests*, Python version and argument vector. Failures/timeouts
are retained, never recorded as PASS. Completed matching cases are skipped.
No script is executed merely by importing this module.

Usage:
 python scripts/run_hopf369_br39_42_bounded.py --part frontier --output /tmp/hopf-receipts\n python scripts/run_hopf369_br39_42_bounded.py --part closure --output /tmp/hopf-receipts\n python scripts/run_hopf369_br39_42_bounded.py --part fast --output /tmp/hopf-receipts
 python scripts/run_hopf369_br39_42_bounded.py --part heavy --output /tmp/hopf-receipts
 python scripts/run_hopf369_br39_42_bounded.py --part all --output /tmp/hopf-receipts

The native Agda kernel must be executed separately; script PASS != kernel PASS.
"""
import argparse, hashlib, json, os, subprocess, sys, time
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
SCRIPTS=ROOT/"scripts"
PARTS={
  "fast":[
    ("BR39", "check_hopf369_br39_physical_cutoff.py",()),
    ("BR40.time","check_hopf369_br40_physical_time_weld.py",("--part","time")),
    ("BR40.trace","check_hopf369_br40_physical_time_weld.py",("--part","trace")),
    ("BR40.subsidiary","check_hopf369_br40_physical_time_weld.py",("--part","subsidiary")),
    ("BR40.graph","check_hopf369_br40_physical_time_weld.py",("--part","graph")),
    ("BR40.projector.small","check_hopf369_br40_variable_projector_transport.py",("--part","small")),
    ("BR41.work","check_hopf369_br41_signed_wall_work_budget.py",()),
    ("BR41.holonomy","check_hopf369_br41_normal_holonomy_projection.py",()),
    ("BR42.energy","check_hopf369_br42_physical_energy_restart.py",()),
    ("BR43.trace.warp","check_hopf369_br43_two_sided_trace.py",("--sector","warp")),
    ("BR43.trace.loss","check_hopf369_br43_two_sided_trace.py",("--sector","loss")),
    ("BR43.charge","check_hopf369_br43_trace_energy_weld.py",()),
    ("BR44.two_level","check_hopf369_br44_two_level_energy.py",()),
    ("BR45.coefficient_growth","check_hopf369_br45_coefficient_growth.py",()),
    ("BR45.energy_ledger","check_hopf369_br45_differentiated_br4.py",("--sector","ledger")),
    ("BR48.adm_collar","check_hopf369_br48_adm_boundary_geometry.py",("--part","collar")),
    ("BR48.shift_guard","check_hopf369_br48_adm_boundary_geometry.py",("--part","shift")),
    ("BR49.graph","check_hopf369_br49_moving_wall_conormal.py",("--part","graph")),
    ("BR49.channels","check_hopf369_br49_moving_wall_conormal.py",("--part","channels")),
    ("BR50.wall_source","check_hopf369_br50_material_energy_weld.py",("--part","source")),
    ("BR51.defect_algebra","check_hopf369_br51_graph_defect_budget.py",("--part","algebra")),
    ("BR51.defect_budget","check_hopf369_br51_graph_defect_budget.py",("--part","budget")),
    ("BR51.defect_channels","check_hopf369_br51_graph_defect_budget.py",("--part","channels")),
    ("BR52.negative","check_hopf369_br52_all_order_material_flux.py",("--part","negative")),
    ("BR53.small","check_hopf369_br53_physical_bianchi_factor.py",("--part","small")),
    ("BR54.negative","check_hopf369_br54_mixed_material_tame.py",("--part","negative")),
    ("BR55.curved","check_hopf369_br55_curved_bianchi_source.py",("--part","curved")),
    ("BR55.boundary","check_hopf369_br55_curved_bianchi_source.py",("--part","boundary")),
    ("BR56.energy","check_hopf369_br56_tame_graph_energy.py",("--part","energy")),
    ("BR56.refusal","check_hopf369_br56_tame_graph_energy.py",("--part","refusal")),
    ("BR57.constants","check_hopf369_br57_curvature_normal_inverse.py",("--part","constants")),
    ("BR59.flat","check_hopf369_br59_full_moving_israel_geometry.py",("--part","flat")),
    ("BR59.warped","check_hopf369_br59_full_moving_israel_geometry.py",("--part","warped")),
    ("BR59.shift","check_hopf369_br59_full_moving_israel_geometry.py",("--part","shift")),
    ("BR60.shape_negative","check_hopf369_br60_moving_israel_frechet.py",("--part","negative")),
    ("BR61.junction","check_hopf369_br61_two_face_nonlinear_israel.py",("--part","rows")),
    ("BR61.unmatched","check_hopf369_br61_two_face_nonlinear_israel.py",("--part","refusal")),
    ("BR62.codazzi","check_hopf369_br62_israel_codazzi_rank.py",()),
    ("BR63.eta","check_hopf369_br63_nonlinear_israel_inverse.py",("--part","reference")),
    ("BR63.moving","check_hopf369_br63_nonlinear_israel_inverse.py",("--part","moving")),
    ("BR63.null","check_hopf369_br63_nonlinear_israel_inverse.py",("--part","source")),
    ("BR64.bidi","check_hopf369_br64_full_israel_optical_bidi.py",("--part","bidi")),
    ("BR64.negative","check_hopf369_br64_full_israel_optical_bidi.py",("--part","negative")),
    ("BR65.geometry","check_hopf369_br65_optical_geometric_israel_weld.py",("--part","geometry")),
    ("BR65.reference","check_hopf369_br65_optical_geometric_israel_weld.py",("--part","reference")),
    ("BR66.mean","check_hopf369_br66_nonzero_mean_israel_weld.py",()),
    ("BR67.coeff","check_hopf369_br67_eighth_order_israel_source.py",("--part","coeff")),
    ("BR68.gauge","check_hopf369_br68_physical_gauge_mean.py",("--part","gauge")),
    ("BR68.mean","check_hopf369_br68_physical_gauge_mean.py",("--part","mean")),
    ("BR69.tower","check_hopf369_br69_physical_gauge_mean_tower.py",("--part","all")),
    ("BR70.frame","check_hopf369_br70_moving_gauge_frame.py",("--part","frame")),
    ("BR70.shift","check_hopf369_br70_moving_gauge_frame.py",("--part","shift")),
    ("BR70.negative","check_hopf369_br70_moving_gauge_frame.py",("--part","negative")),
    ("BR71.physical","check_hopf369_br71_full_physical_de_rows.py",("--part","all")),
    ("BR73.algebra","check_hopf369_br73_adm_normal_energy.py",("--part","algebra")),
    ("BR73.negative","check_hopf369_br73_adm_normal_energy.py",("--part","negative")),
    ("BR73.channels","check_hopf369_br73_adm_normal_energy.py",("--part","channels")),
    ("BR74.jet","check_hopf369_br74_nonlinear_graph_codazzi.py",("--part","jet")),
    ("BR74.rank","check_hopf369_br74_nonlinear_graph_codazzi.py",("--part","rank")),
    ("BR75.algebra","check_hopf369_br75_nonlinear_graph_gauss.py",("--part","algebra")),
    ("BR75.refusal","check_hopf369_br75_nonlinear_graph_gauss.py",("--part","refusal")),
    ("BR76.moving","check_hopf369_br76_adm_moving_energy_flux.py",("--part","moving")),
    ("BR77.decomposition","check_hopf369_br77_wall_flux_coercivity.py",("--part","decomposition")),
    ("BR77.sharp","check_hopf369_br77_wall_flux_coercivity.py",("--part","sharp")),
    ("BR77.channels","check_hopf369_br77_wall_flux_coercivity.py",("--part","channels")),
    ("BR77.negative","check_hopf369_br77_wall_flux_coercivity.py",("--part","negative")),
    *[(f"BR78.{part}","check_hopf369_br78_tension_bianchi_ward.py",("--part",part)) for part in ("vacuum","matter","symbol","negative")],
  ],
  "heavy":[
    *[(f"BR{k}.{part}","check_hopf369_br175_177_reflection_radial.py",("--part",part)) for k,part in ((175,"split"),(176,"paired"),(177,"radial"))],
    *[(f"BR{k}.{part}","check_hopf369_br172_174_joint.py",("--part",part)) for k,part in ((172,"atomic"),(173,"inverse"),(174,"wall"))],
    *[(f"BR{k}.{part}","check_hopf369_br169_171_bound_trace.py",("--part",part)) for k,part in ((169,"pauli"),(170,"shell"),(171,"grazing"))],
    *[(f"BR{k}.{part}","check_hopf369_br165_168_parallel.py",("--part",part)) for k,part in ((165,"donor"),(166,"spin"),(167,"symbol"),(168,"region"))],
    *[(f"BR{k}.{part}","check_hopf369_br161_164_parallel.py",("--part",part)) for k,part in ((161,"york"),(162,"atomic"),(163,"pauli"),(164,"cartan"))],
    *[(f"BR{k}.{part}","check_hopf369_br157_160_parallel.py",("--part",part)) for k,part in ((157,"ls"),(158,"residual"),(159,"frames"),(160,"quadrupole"))],
    *[(f"BR{k}.{part}","check_hopf369_br154_156_atomic.py",("--part",part)) for k,part in ((154,"chars"),(155,"lane"),(156,"coulomb"))],
    *[(f"BR{k}.{part}","check_hopf369_br150_153_parallel.py",("--part",part)) for k,part in ((150,"trace"),(151,"optics"),(152,"york"),(153,"leech"))],
    *[(f"BR{k}.{part}","check_hopf369_br146_149_parallel.py",("--part",part)) for k,part in ((146,"normal"),(147,"optical"),(148,"rmhd"),(149,"observer"))],
    *[(f"BR{k}.{part}","check_hopf369_br143_145_parallel.py",("--part",part)) for k,part in ((143,"trace"),(144,"tides"),(145,"quotient"))],
    *[(f"BR{k}.{part}","check_hopf369_br140_142_F_surface_cartan.py",("--part",part)) for k,part in ((140,"jump"),(141,"shear"),(142,"transport"))],
    *[(f"BR{k}.{part}","check_hopf369_br136_139_F_variable_subsidiary.py",("--part",part)) for k,part in ((136,"mean"),(137,"current"),(138,"torsion"),(139,"trace"))],
    *[(f"BR{k}.{part}","check_hopf369_br132_135_F_bianchi_cartan.py",("--part",part)) for k,part in ((132,"graph"),(133,"wall"),(134,"exterior"),(135,"cartan"))],
    *[(f"BR{k}.{part}","check_hopf369_br128_131_F_curvature_development.py",("--part",part)) for k,part in ((128,"material"),(129,"defect"),(130,"weighted"),(131,"cartan"))],
    *[(f"BR{k}.{part}","check_hopf369_br124_127_F_gauss_weyl.py",("--part",part)) for k,part in ((124,"gauss"),(125,"electric"),(126,"split"),(127,"riccati"))],
    *[(f"BR{k}.{part}","check_hopf369_br120_123_F_source_transport.py",("--part",part)) for k,part in ((120,"jump"),(121,"chart"),(122,"commutator"),(123,"null"))],
    *[(f"BR{k}.{part}","check_hopf369_br116_119_F_structured_scale.py",("--part",part)) for k,part in ((116,"ak"),(117,"shear"),(118,"foliation"),(119,"robin"))],
    *[(f"BR{k}.{part}","check_hopf369_br112_115_F_finite_generator.py",("--part",part)) for k,part in ((112,"graph"),(113,"reference"),(114,"finite"),(115,"neumann"))],
    *[(f"BR{k}.{part}","check_hopf369_br108_111_F_wave_adapted_lift.py",("--part",part)) for k,part in ((108,"lift"),(109,"joint"),(110,"glancing"),(111,"naturality"))],
    *[(f"BR{k}.{part}","check_hopf369_br104_107_F_curved_wall_wave.py",("--part",part)) for k,part in ((104,"normal"),(105,"wall"),(106,"tau"),(107,"trace"))],
    *[(f"BR{k}.{part}","check_hopf369_br100_103_F_normal_inverse.py",("--part",part)) for k,part in ((100,"normal"),(101,"jacobian"),(102,"energy"),(103,"warp"))],
    ("BR96.reflection","check_hopf369_br96_99_continuous_gauge.py",("--part","reflection")),
    *[(f"BR97.{part}.{sector}","check_hopf369_br96_99_continuous_gauge.py",("--part",part,"--sector",sector)) for part in ("rest","ray") for sector in ("metric","gauge")],
    ("BR97.finite","check_hopf369_br96_99_continuous_gauge.py",("--part","finite")),
    ("BR98.energy","check_hopf369_br96_99_continuous_gauge.py",("--part","energy")),
    ("BR99.warp","check_hopf369_br96_99_continuous_gauge.py",("--part","warp")),
    *[(f"BR{k}.{part}","check_hopf369_br92_95_folded_subsidiary.py",("--part",part)) for k,part in ((92,"bianchi"),(93,"fold"),(94,"energy"),(95,"symbol"))],
    ("BR89.algebra","check_hopf369_br89_91_warped_cotton_weld.py",("--part","algebra")),
    *[(f"BR89.{sector}.{k}","check_hopf369_br89_91_warped_cotton_weld.py",("--part","warp","--sector",sector,"--sample",str(k))) for sector in ("metric","gauge") for k in range(3)],
    ("BR90.jump","check_hopf369_br89_91_warped_cotton_weld.py",("--part","jump")),
    ("BR91.cotton","check_hopf369_br89_91_warped_cotton_weld.py",("--part","cotton")),
    ("BR85.geometry","check_hopf369_br85_88_geometric_weld.py",("--part","BR85")),
    ("BR86.energy","check_hopf369_br85_88_geometric_weld.py",("--part","BR86")),
    *[(f"BR87.{a}.{b}","check_hopf369_br85_88_geometric_weld.py",("--part","BR87","--allocation",a,"--sector",b)) for a in ("D","E") for b in ("metric","gauge")],
    ("BR88.projector","check_hopf369_br85_88_geometric_weld.py",("--part","BR88")),
    *[(f"BR82.{part}","check_hopf369_br82_glancing_loss.py",("--part",part)) for part in ("algebra","growth","refusal")],
    *[(f"BR83.{part}","check_hopf369_br83_full_5d_energy_current.py",("--part",part)) for part in ("full","channels","moving","negative")],
    *[(f"BR84.{part}","check_hopf369_br84_bn_wall_corner.py",("--part",part)) for part in ("corner","inverse","negative")],
    ("BR79.initial","check_hopf369_br79_bn_adm_initial_bridge.py",("--part","cauchy")),
    ("BR79.momentum","check_hopf369_br79_bn_adm_initial_bridge.py",("--part","momentum")),
    ("BR79.owners","check_hopf369_br79_bn_adm_initial_bridge.py",("--part","owners")),
    ("BR80.current","check_hopf369_br80_adm_energy_current.py",("--part","current")),
    ("BR80.stress","check_hopf369_br80_adm_energy_current.py",("--part","stress")),
    ("BR80.source","check_hopf369_br80_adm_energy_current.py",("--part","source")),
    ("BR80.refusal","check_hopf369_br80_adm_energy_current.py",("--part","refusal")),
    *[(f"BR81.{p}","check_hopf369_br81_existing_ak_bn_lapse_bridge.py",("--part",p)) for p in ("reference","lapse","junction","refusal")],
    ("BR74.graph","check_hopf369_br74_nonlinear_graph_codazzi.py",("--part","graph")),
    ("BR75.sample","check_hopf369_br75_nonlinear_graph_gauss.py",("--part","sample")),
    ("BR76.formula","check_hopf369_br76_adm_moving_energy_flux.py",("--part","formula")),
    ("BR76.channels","check_hopf369_br76_adm_moving_energy_flux.py",("--part","channels")),
    *[(f"BR72.{alloc}.{k}","check_hopf369_br72_unified_eighth_order_boundary.py",("--allocation",alloc,"--order",str(k))) for alloc in ("D","E") for k in range(9)],
    ("BR67.physical","check_hopf369_br67_eighth_order_israel_source.py",("--part","physical")),
    *[(f"BR60.K.{i}","check_hopf369_br60_moving_israel_frechet.py",("--part","component","--index",str(i))) for i in range(10)],
    ("BR52.metric","check_hopf369_br52_all_order_material_flux.py",("--part","metric")),
    ("BR52.gauge","check_hopf369_br52_all_order_material_flux.py",("--part","gauge")),
    ("BR53.physical","check_hopf369_br53_physical_bianchi_factor.py",("--part","physical")),
    *[(f"BR54.{sector}.{multi}","check_hopf369_br54_mixed_material_tame.py",("--part",sector,"--multi",multi)) for sector in ("metric","gauge") for multi in ("2,2,2,2","8,0,0,0","0,8,0,0","0,0,0,8","4,2,1,1")],
    ("BR55.flat","check_hopf369_br55_curved_bianchi_source.py",("--part","flat")),
    ("BR56.coeff","check_hopf369_br56_tame_graph_energy.py",("--part","coeff")),
    *[(f"BR57.normal.{k}","check_hopf369_br57_curvature_normal_inverse.py",("--part","channel","--component",str(k))) for k in range(16)],
    *[(f"BR58.{sector}.{alloc}","check_hopf369_br58_material_boundary_jets.py",("--sector",sector,"--allocation",alloc)) for sector in ("metric","gauge") for alloc in ("D","E")],
    ("BR48.variable_source","check_hopf369_br48_adm_boundary_geometry.py",("--part","source")),
    *[(f"BR47.{sector}.{alloc}.{k}","check_hopf369_br47_boundary_hierarchy.py",("--sector",sector,"--allocation",alloc,"--order",str(k))) for sector in ("metric","gauge") for alloc in ("D","E") for k in range(9)],
    *[(f"BR45.metric.{k}","check_hopf369_br45_differentiated_br4.py",("--sector","metric","--component",str(k))) for k in range(15)],
    *[(f"BR45.gauge.{k}","check_hopf369_br45_differentiated_br4.py",("--sector","gauge","--component",str(k))) for k in range(5)],
    *[(f"BR46.bianchi.{k}","check_hopf369_br46_bianchi_source_weld.py",("--component",str(k))) for k in range(5)],
    ("BR43.trace.metric","check_hopf369_br43_two_sided_trace.py",("--sector","metric")),
    ("BR43.trace.gauge","check_hopf369_br43_two_sided_trace.py",("--sector","gauge")),
    ("BR40.projector.physical","check_hopf369_br40_variable_projector_transport.py",("--part","physical")),
    *[(f"BR40.warp.covector.{k}","check_hopf369_br40_warped_connection.py",
       ("--sector","covector","--index",str(k))) for k in range(5)],
    *[(f"BR40.warp.tensor.{k}","check_hopf369_br40_warped_connection.py",
       ("--sector","tensor","--index",str(k))) for k in range(25)],
    ("BR40.warp.scalar","check_hopf369_br40_warped_connection.py",
     ("--sector","scalar","--index","0")),
  ]
}

# Terminal source checks, independently checkpointed.
PARTS["terminal"]=[
 ("BR178.symbol","check_hopf369_br178_180_cartan_radial.py",("--part","symbol")),
 ("BR180.radial","check_hopf369_br178_180_cartan_radial.py",("--part","radial")),
 *[(f"BR181185.{p}","check_hopf369_br181_185_terminal_bridges.py",("--part",p)) for p in ("cartan","radial","shell","observables","material")],
 ("BR186.shell","check_hopf369_br186_interacting_shell.py",()),
 ("BR187.atomic","check_hopf369_br187_188_full_shell_lifespan.py",("--part","atomic")),
 ("BR188.lifespan","check_hopf369_br187_188_full_shell_lifespan.py",("--part","lifespan")),
]

PARTS["terminal"] += [(f"BR189191.{p}","check_hopf369_br189_191_endpoint_bounds.py",("--part",p)) for p in ("g3","g4","cartan")]

PARTS["terminal"] += [(f"BR192196.{p}","check_hopf369_br192_196_source_endpoint.py",("--part",p)) for p in ("cartan","g3","g4","material","monster")]

PARTS["terminal"] += [(f"BR197201.{p}","check_hopf369_br197_201_terminal_welds.py",("--part",p)) for p in ("cartan","marked","analytic","primitive","receiver")]

PARTS["terminal"].append(("BR202.projector","check_hopf369_br202_physical_projector.py",()))

PARTS["terminal"].append(("BR203.moving_projector","check_hopf369_br203_moving_physical_projector.py",()))

PARTS["terminal"].append(("BR204.boost_null","check_hopf369_br204_boost_null.py",()))

PARTS["terminal"].append(("BR205.wall_lorentz","check_hopf369_br205_wall_lorentz.py",()))

PARTS["terminal"].append(("BR207.moving_normal","check_hopf369_br207_moving_normal.py",()))

PARTS["terminal"].append(("BR208.joint_flux","check_hopf369_br208_joint_flux.py",()))

PARTS["terminal"].append(("BR209.bianchi_energy","check_hopf369_br209_bianchi_energy.py",()))

PARTS["terminal"].append(("BR210.collar_trace","check_hopf369_br210_collar_trace.py",()))

PARTS["terminal"].append(("BR211.static_evanescent","check_hopf369_br211_static_evanescent.py",()))

PARTS["terminal"].append(("BR212.glancing_pencil","check_hopf369_br212_glancing_pencil.py",()))

PARTS["terminal"].append(("BR213.glancing_filtration","check_hopf369_br213_glancing_filtration.py",()))

PARTS["terminal"].append(("BR214.frequency_compactification","check_hopf369_br214_frequency_compactification.py",()))

PARTS["terminal"].append(("BR215.damped_scale","check_hopf369_br215_damped_scale.py",()))

PARTS["terminal"].append(("BR216.selective_wall_weight","check_hopf369_br216_selective_wall_weight.py",()))

PARTS["terminal"].append(("BR217.regularized_inverse","check_hopf369_br217_regularized_inverse.py",()))

PARTS["terminal"].append(("BR218.forced_boundary_lift","check_hopf369_br218_forced_boundary_lift.py",()))

PARTS["terminal"].append(("BR219.exterior_source_inverse","check_hopf369_br219_exterior_source_inverse.py",()))

PARTS["terminal"].append(("BR220.normal_constraint_propagation","check_hopf369_br220_normal_constraint_propagation.py",()))

PARTS["terminal"].append(("BR221.finite_physical_transmission","check_hopf369_br221_finite_physical_transmission.py",()))

PARTS["terminal"].append(("BR222.intrinsic_particular","check_hopf369_br222_intrinsic_particular.py",()))

PARTS["terminal"].append(("BR223.regular_complement","check_hopf369_br223_regular_complement.py",()))

PARTS["terminal"].append(("BR224.composed_energy","check_hopf369_br224_composed_energy.py",()))

PARTS["terminal"] += [(f"BR225229.{p}","check_hopf369_br225_229_endpoint_welds.py",("--part",p)) for p in ("periodic","g3","g4","material","atomic")]

PARTS["terminal"] += [(f"BR230233.{p}","check_hopf369_br230_233_dynamic_cut.py",("--part",p)) for p in ("periodic","g4","material")]

PARTS["terminal"] += [(f"BR237239.{p}","check_hopf369_br237_239_geometry.py",("--part",p)) for p in ("wall","material","scaling")]

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def manifest_hash():
    # Include all directly used original operators and test sources; changes
    # anywhere relevant invalidate cached PASS. This is intentionally
    # conservative: new source commits force independent replay.
    # Include all original spatial constraint producers (BL/BM/BN/AK),
    # as well as BR/BS consumers and pinned source receipts. Without
    # these a cached PASS could survive a change to the source operator.
    paths=sorted(SCRIPTS.glob("check_hopf369_*.py"))
    paths+=sorted(SCRIPTS.glob("hopf369_*.py"))
    paths+=sorted((ROOT/"DASHI/Physics/Foundations").glob("Hopf369*.agda"))
    path_artifacts=ROOT/"Artifacts/hopf369"
    if path_artifacts.is_dir():
        paths+=sorted(p for p in path_artifacts.rglob("*") if p.is_file())
    paths.append(Path(__file__).resolve())
    h=hashlib.sha256()
    for p in paths:
        if not p.is_file(): continue
        h.update(str(p.relative_to(ROOT)).encode());h.update(p.read_bytes())
    h.update(sys.version.encode())
    return h.hexdigest()

def atomic_json(path,obj):
    tmp=path.with_suffix(".tmp")
    with tmp.open("w") as out:
        json.dump(obj,out,indent=2,sort_keys=True)
        out.flush();os.fsync(out.fileno())
    os.replace(tmp,path)

def stage(label,script,args,receipts,identity,seconds):
    path=receipts/(label.replace("/","_")+".json")
    cmd=[sys.executable,str(SCRIPTS/script),*args]
    runid=hashlib.sha256(json.dumps([identity,cmd],sort_keys=True).encode()).hexdigest()
    if path.exists():
        previous=json.loads(path.read_text())
        if previous.get("runid")==runid and previous.get("status")=="PASS":
            return "CACHED_PASS"
    environment=dict(os.environ)
    environment.update(OPENBLAS_NUM_THREADS="1",MKL_NUM_THREADS="1",
                       OMP_NUM_THREADS="1",NUMEXPR_NUM_THREADS="1")
    begin=time.monotonic()
    try:
        result=subprocess.run(cmd,cwd=SCRIPTS,env=environment,text=True,
                   stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=seconds)
        status="PASS" if result.returncode==0 else "FAIL"
        output=result.stdout[-14000:];error=result.stderr[-14000:]
        code=result.returncode
    except subprocess.TimeoutExpired as exc:
        status="TIMEOUT"
        output=(exc.stdout or b"")
        error=(exc.stderr or b"")
        if isinstance(output,bytes):output=output.decode("utf-8","replace")
        if isinstance(error,bytes):error=error.decode("utf-8","replace")
        output=output[-14000:];error=error[-14000:]
        code=None
    receipt=dict(name=label,status=status,runid=runid,source_identity=identity,
         command=cmd,returncode=code,elapsed_seconds=round(time.monotonic()-begin,3),
         stdout=output,stderr=error,acceptance="source checker only; Agda kernel unrun")
    atomic_json(path,receipt)
    return status

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--part",choices=("fast","heavy","frontier","closure","terminal","all"),default="frontier")
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--seconds",type=int,default=90)
    args=parser.parse_args()
    if not 1<=args.seconds<=90:raise ValueError("bounded run: max 90 seconds/case")
    args.output.mkdir(parents=True,exist_ok=True)
    ident=manifest_hash()
    if args.part=="all":
        plans=PARTS["fast"]+PARTS["heavy"]+PARTS["terminal"]
    elif args.part=="closure":
        plans=[p for group in ("fast","heavy") for p in PARTS[group]
               if p[0].split(".")[0] in {"BR79","BR80","BR81","BR82","BR83","BR84","BR85","BR86","BR87","BR88","BR89","BR90","BR91","BR92","BR93","BR94","BR95","BR96","BR97","BR98","BR99","BR100","BR101","BR102","BR103","BR104","BR105","BR106","BR107","BR108","BR109","BR110","BR111","BR112","BR113","BR114","BR115","BR116","BR117","BR118","BR119","BR120","BR121","BR122","BR123","BR124","BR125","BR126","BR127","BR128","BR129","BR130","BR131","BR132","BR133","BR134","BR135","BR136","BR137","BR138","BR139","BR140","BR141","BR142","BR143","BR144","BR145","BR146","BR147","BR148","BR149","BR150","BR151","BR152","BR153","BR154","BR155","BR156","BR157","BR158","BR159","BR160","BR161","BR162","BR163","BR164","BR165","BR166","BR167","BR168","BR169","BR170","BR171","BR172","BR173","BR174","BR175","BR176","BR177"}]
    elif args.part=="frontier":
        plans=[p for group in ("fast","heavy") for p in PARTS[group]
               if p[0].split(".")[0] in {"BR52","BR53","BR54","BR55","BR56","BR57","BR58","BR59","BR60","BR61","BR62","BR63","BR64","BR65","BR66","BR67","BR68","BR69","BR70","BR71","BR72","BR73","BR74","BR75","BR76","BR77","BR78","BR79","BR80","BR81","BR82","BR83","BR84","BR85","BR86","BR87","BR88","BR89","BR90","BR91","BR92","BR93","BR94","BR95","BR96","BR97","BR98","BR99","BR100","BR101","BR102","BR103","BR104","BR105","BR106","BR107","BR108","BR109","BR110","BR111","BR112","BR113","BR114","BR115","BR116","BR117","BR118","BR119","BR120","BR121","BR122","BR123","BR124","BR125","BR126","BR127","BR128","BR129","BR130","BR131","BR132","BR133","BR134","BR135","BR136","BR137","BR138","BR139","BR140","BR141","BR142","BR143","BR144","BR145","BR146","BR147","BR148","BR149","BR150","BR151","BR152","BR153","BR154","BR155","BR156","BR157","BR158","BR159","BR160","BR161","BR162","BR163","BR164","BR165","BR166","BR167","BR168","BR169","BR170","BR171","BR172","BR173","BR174","BR175","BR176","BR177"}]
    else:
        plans=PARTS[args.part]
    if args.part in ("closure","frontier"): plans += PARTS["terminal"]
    outcome={}
    for label,script,opts in plans:
        outcome[label]=stage(label,script,opts,args.output,ident,args.seconds)
        print(label,outcome[label],flush=True)
    atomic_json(args.output/"summary.json",dict(source_identity=ident,part=args.part,
          outcomes=outcome,all_accepted=all(v in ("PASS","CACHED_PASS") for v in outcome.values()),
          native_kernel_accepted=False,physical_pde_theorem_accepted=False))
    if any(v not in ("PASS","CACHED_PASS") for v in outcome.values()):sys.exit(1)

if __name__=="__main__":main()
