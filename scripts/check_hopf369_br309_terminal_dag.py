"""BR309 all-lane source/proof acceptance DAG, no truth promotion.
Never turn finite checks or source-written code into a theorem PASS.
"""
import argparse,copy,json
from collections import defaultdict
from pathlib import Path
LANES=('periodic','atomic','g3','g4','hyperfabric','monster','material')
STATUSES=('accepted_source','executed_finite','written_unrun','conditional','held')

def audit(data):
    nodes=data['nodes']; assert len(nodes)==len(set(nodes))
    for key,item in nodes.items():
        assert item['lane'] in LANES+('shared',)
        assert item['status'] in STATUSES
        assert isinstance(item['owner'],str) and len(item['owner'])>3
        assert isinstance(item['deps'],list)
        assert all(x in nodes for x in item['deps']),key
        assert key not in item['deps']
        if item['status'] in ('conditional','held'):
            assert item.get('unpaid') and isinstance(item['unpaid'],str)
        if item.get('endpoint'):
            assert item['status']!='executed_finite',key
    state={};ordered=[]
    def visit(k):
        if state.get(k)==1:raise ValueError('dependency cycle '+k)
        if state.get(k)==2:return
        state[k]=1
        for d in nodes[k]['deps']:visit(d)
        state[k]=2;ordered.append(k)
    for k in nodes:visit(k)
    for lane in LANES:
        endpoints=[k for k,x in nodes.items() if x['lane']==lane and x.get('endpoint')]
        assert len(endpoints)==1,(lane,endpoints)
        target=nodes[endpoints[0]]
        assert target['status']=='held' and target.get('unpaid')
    accepted={'accepted_source','executed_finite'}
    def blockers(k):
        out=[]
        for d in nodes[k]['deps']:
            if nodes[d]['status'] not in accepted:out.append(d)
            out.extend(blockers(d))
        return list(dict.fromkeys(out))
    frontier=[k for k in ordered if nodes[k]['status'] not in accepted and not blockers(k)]
    pending={k:blockers(k) for k in ordered if nodes[k]['status'] not in accepted}
    return ordered,frontier,pending

def checks(data):
    order,frontier,pending=audit(data)
    bad=copy.deepcopy(data); name=next(iter(bad['nodes']));bad['nodes'][name]['deps'].append('nonexistent')
    try:audit(bad);raise AssertionError('unknown owner incorrectly accepted')
    except AssertionError as e:
        if str(e)=='unknown owner incorrectly accepted':raise
    bad=copy.deepcopy(data);a,b=list(bad['nodes'])[:2];bad['nodes'][a]['deps']=[b];bad['nodes'][b]['deps']=[a]
    try:audit(bad);raise AssertionError('cycle incorrectly accepted')
    except ValueError:pass
    bad=copy.deepcopy(data);ep=next(k for k,v in bad['nodes'].items() if v.get('endpoint'));bad['nodes'][ep]['status']='executed_finite'
    try:audit(bad);raise AssertionError('finite endpoint promotion accepted')
    except AssertionError as e:
        if str(e)=='finite endpoint promotion accepted':raise
    print('BR309 PASS 7 independent held endpoints, full source DAG',len(order),'nodes; negative tests unknown/cycle/false promotion',flush=True)
    print('BR309 actual minimal frontier',json.dumps(frontier),flush=True)
    for lane in LANES:
        k=next(k for k,v in data['nodes'].items() if v['lane']==lane and v.get('endpoint'))
        print('BR309',lane,'held by',json.dumps(pending[k]),'unpaid',data['nodes'][k]['unpaid'],flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--manifest',type=Path,default=Path(__file__).with_name('br309_terminal_dependency_manifest.json'))
    a=p.parse_args();checks(json.loads(a.manifest.read_text()))
