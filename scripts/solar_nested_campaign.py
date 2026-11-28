"""Explicitly matched parent material and independent nested port chart.

The source/receiver ports must be given for the fine mesh. This is a
discretization comparison, not evidence of identical physical impedance.
"""
import numpy as np
from solar_spherical_material_weld import assembly_mesh,construct
from solar_spherical_cycle import cycle,geometry
from solar_nested_cochain_refinement import nested_cochains,metric_pullback,material_cell_maps
from solar_evolution_residual import field_maps,coefficient_reopen
from solar_spherical_reverse_jvp import campaign_jvp
from solar_earth_collision_tensor import rates

def nested_problem(material,cfg,fine_ports):
    if cfg.get('nested_depth',0) or not cfg.get('fixed_horizon',True):
        raise ValueError('one nested refinement of fixed original horizon required')
    xyz,s,m,d=assembly_mesh(tuple(cfg['radii_m']),int(cfg['angular_level']),0)
    b=nested_cochains(xyz,s);cells=material_cell_maps(b,xyz,s);owner=cells['owner']
    ratio=cells['fine_volumes']/cells['coarse_volumes'][owner]
    if not np.allclose(ratio,1/24,rtol=1e-12,atol=0):
        raise ValueError('uniform barycentric child volume required by shared reaction coefficient')
    rows,neutral,D,gyro,axis=material
    fm=([dict(rows[i]) for i in owner],np.asarray(neutral)[owner],np.asarray(D)[owner],
        np.asarray(gyro)[owner],np.asarray(axis)[owner])
    fc=dict(cfg,nested_depth=1,sparse_operator=True,common_stage_atlas=True,retain_history=True,retain_sensitivity=True)
    if not {'source_edge','source_coupling_sqrt_inv_s','load_rate_s_inv','return_atol'}<=set(fine_ports):
        raise ValueError('independent fine source/receiver and return allowance required')
    for name in ('source_edge','source_coupling_sqrt_inv_s','load_rate_s_inv','terminal_load_rate_s_inv','return_atol'):
        if name in fine_ports:fc[name]=fine_ports[name]
    if 'terminal_load_rate_s_inv' in cfg and 'terminal_load_rate_s_inv' not in fine_ports:
        raise ValueError('explicit fine terminal receiver required')
    fc['row_keys']=[str(cfg['row_keys'][i])+':nested:'+str(j) for j,i in enumerate(owner)]
    fc['heating_W']=np.asarray(cfg['heating_W'])[:,owner]/24
    for k in ('heat_capacity_J_K','cooling_W_K'):fc[k]=np.asarray(cfg[k])[owner]/24
    q=dict(cfg['kinetics'])
    for k in ('initial_neutral_m3','birth_velocity_m_s'):q[k]=np.asarray(q[k])[owner]
    # Preserve intensive reaction and thermal rates, total heating/capacity.
    q['heater_ionization_per_J']=24*np.asarray(q['heater_ionization_per_J'])
    fc['kinetics']=q
    cv,_,ne,nf=geometry(cfg['radii_m'],cfg['angular_level'])
    fv,_,fe,ff=geometry(cfg['radii_m'],cfg['angular_level'],1)
    if np.asarray(fc['load_rate_s_inv']).shape!=(fe,):
        raise ValueError('fine load chart shape mismatch')
    cm=construct(cfg['radii_m'],cfg['angular_level'],np.arange(len(cv)),cv,D,rates(rows,neutral),gyro,axis)
    ffmodel=construct(cfg['radii_m'],cfg['angular_level'],np.arange(len(fv)),fv,fm[2],rates(fm[0],fm[1]),fm[3],fm[4],nested_depth=1)
    metric=metric_pullback(b,cm['consistent_masses'],ffmodel['consistent_masses'])
    L,R=field_maps(metric,cells)
    return fm,fc,L,R,cells,dict(coarse_size=ne+nf+9*len(cv),fine_size=fe+ff+9*len(fv),
        physical_port_equivalence_admitted=False,
        diagonal_metric_defects=[v['diagonal_relative_defect'] for v in metric])

def compare_nested(material,cfg,fine_ports,dheating=None,dload=None,fine_dload=None):
    fm,fc,L,R,cells,meta=nested_problem(material,cfg,fine_ports)
    cc=dict(cfg,common_stage_atlas=True,retain_history=True,retain_sensitivity=True)
    coarse=cycle(material,cc)
    shadow=dict(prolongation=L,endpoints=np.asarray(coarse['history'])[:,:L.shape[1]],
        useful_J=[v['useful_J'] for v in coarse['sensitivity_trace']])
    fine=cycle(fm,fc,shadow=shadow)
    history=coefficient_reopen(np.asarray(fine['history'])[:,:L.shape[0]],
        shadow['endpoints'],L,R)
    result=dict(coarse=coarse,fine=fine,geometry=meta,base_reopen_error=history['reconstruction_error'],
        signed_field_residual=history['signed_residual'].tolist(),field_complement=history['complement'].tolist(),
        physical_admission=False)
    # Intensive material states use volume-weighted restriction, not the
    # energy-coordinate lift applied to normalized current.
    from scipy.sparse import kron,eye
    def material_reopen(fh,ch,width):
        mL=kron(cells['density_prolongation'],eye(width),format='csr')
        mR=kron(cells['density_restriction'],eye(width),format='csr')
        out=coefficient_reopen(fh,ch,mL,mR)
        return dict(reconstruction_error=out['reconstruction_error'],signed_residual=out['signed_residual'].tolist(),complement=out['complement'].tolist())
    ch=np.asarray(coarse['history']);fh=np.asarray(fine['history']);nc=len(cells['coarse_volumes']);nf=len(cells['fine_volumes'])
    result['material_reopen']={}
    offc=L.shape[1];offf=L.shape[0]
    for name,width in (('population',3),('pool',2),('temperature',1)):
        result['material_reopen'][name]=material_reopen(fh[:,offf:offf+nf*width],ch[:,offc:offc+nc*width],width)
        offc+=nc*width;offf+=nf*width
    if dheating is not None:
        if dload is None or fine_dload is None:
            raise ValueError('independent load direction required on each mesh')
        cc['retain_jet_history']=True;fc['retain_jet_history']=True
        c=campaign_jvp(material,cc,dheating,dload,quadratic_amplitude_path=True,quadratic_second_order=True)
        def fields(j):return np.array([[s[k] for k in ('field','first','second')] for s in j['indexed_jet_history']])
        jet_shadow=dict(prolongation=L,endpoints=fields(c),
            useful_coefficients_J=[s['useful_coefficients_J'] for s in c['indexed_jet_history']])
        f=campaign_jvp(fm,fc,np.asarray(dheating)[:,cells['owner']]/24,fine_dload,
            quadratic_amplitude_path=True,quadratic_second_order=True,shadow=jet_shadow)
        out=coefficient_reopen(fields(f),fields(c),L,R)
        result['jet_reopen']=dict(reconstruction_error=out['reconstruction_error'],
            signed_residual=out['signed_residual'].tolist(),complement=out['complement'].tolist(),
            coefficient_evolution_bound_candidate=f['jet_endpoint_error_bound_candidate'],
            receiver_coefficient_error_bound_candidate_J=f['jet_receiver_work_error_bound_candidate_J'],
            signed_evolution_residual_trace=f['signed_jet_evolution_residual_trace'],
            outward_rounding_certified=False,coefficient_evolution_bound_admitted=False)
        result['material_jet_reopen']={}
        for name,width in (('population',3),('pool',2),('temperature',1),('population_u',3),('pool_u',2),('temperature_u',1),('population_u2',3),('pool_u2',2)):
            def read(j):return np.array([np.asarray(row[name]).ravel() for row in j['indexed_jet_history']])
            result['material_jet_reopen'][name]=material_reopen(read(f),read(c),width)
    return result
