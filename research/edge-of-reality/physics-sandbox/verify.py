"""Cross-check all Lean integer-percent predictions and boundary conditions."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
from physics import (EXE, LABELS, classical_exact, quantum_reference,
                     experiment, compare_import, matmul)

ROOT = Path(__file__).resolve().parent
output = subprocess.run([str(EXE),'--grid'],capture_output=True,text=True,
                        check=True,timeout=30)
count, max_error = 0, 0
for line in output.stdout.splitlines():
    r = json.loads(line)
    p,l = r['p'],r['l']
    expected = classical_exact(p,l)
    actual = tuple(Fraction(m,r['denominator']) for m in r['masses'])
    assert actual == expected, (p,l,'exact disagreement')
    assert sum(actual) == 1 and all(x >= 0 for x in actual)
    quantum = quantum_reference(p,l)
    error = max(abs(float(a)-b) for a,b in zip(actual,quantum))
    assert error < 1e-12, (p,l,'matrix disagreement')
    max_error = max(max_error,error)
    posterior = r['posteriorZero']
    success = actual[0]+actual[1]
    if success:
        assert Fraction(posterior['numerator'],posterior['denominator']) == actual[0]/success
    else:
        assert posterior is None
    edges = r['interfaces']
    assert len(edges)==6
    for e in edges:
        assert e['admissible'] == (e['mass']>0)
    by_id={e['id']:e for e in edges}
    assert by_id['filterSuccess']['mass']==r['successMass']
    assert by_id['filterFailure']['mass']==r['failureMass']
    assert by_id['readSuccess0']['mass']==r['masses'][0]
    assert by_id['readSuccess1']['mass']==r['masses'][1]
    assert by_id['readFailure0']['mass']==0
    assert by_id['readFailure1']['mass']==r['failureMass']
    assert by_id['readSuccess0']['coarseRecord']==by_id['readSuccess1']['coarseRecord']
    assert by_id['readSuccess0']['resolvedRecord']!=by_id['readSuccess1']['resolvedRecord']
    count += 1
assert count == 10201

# Independently assemble the exported controlled-Ry decomposition.
for lam in range(101):
    import math
    angle = math.acos(lam/100)
    def rotation(a):
        c,s=math.cos(a/2),math.sin(a/2)
        return [[c,-s,0,0],[s,c,0,0],[0,0,c,-s],[0,0,s,c]]
    cx=[[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]]
    decomposition=matmul(cx,matmul(rotation(-angle),matmul(cx,rotation(angle))))
    c,s=lam/100,math.sqrt(1-(lam/100)**2)
    target=[[1,0,0,0],[0,1,0,0],[0,0,c,-s],[0,0,s,c]]
    assert max(abs(decomposition[i][j]-target[i][j]) for i in range(4) for j in range(4))<1e-12

r = experiment(50,50,10000,42)
assert r['quantum']['expectedSuccess'] == .625
assert r['quantum']['expectedConditionalZero'] == .8
assert r == experiment(50,50,10000,42), 'seed reproducibility'
for engine in ('quantum','classical'):
    counts=r[engine]['counts']
    assert sum(counts.values())==10000
    assert counts['failure0']==0
    for k,prob in zip(LABELS,classical_exact(50,50)):
        assert abs(counts[k]-10000*float(prob)) < 8*(10000*float(prob)*(1-float(prob)))**.5+1
zero=experiment(0,0,100,42)
assert zero['lean']['posteriorZero'] is None
assert zero['quantum']['conditionalZero'] is None
assert zero['quantum']['counts']['failure1']==100
transparent=experiment(50,100,100,42)
assert transparent['quantum']['successRate']==1

valid={'schema':'ER01-COUNTS/1','pPercent':50,'lambdaPercent':50,
       'shots':10000,'samplingDesign':'iid-mixture','source':'synthetic verification',
       'counts':dict(zip(LABELS,[5000,1250,0,3750]))}
assert compare_import(valid)['summary']['successRate']==.625
assert compare_import(valid)['provenance']=='USER_SUPPLIED_COUNTS_UNVERIFIED'
for malformed in [dict(valid,shots=9999),dict(valid,pPercent=True),
                  dict(valid,counts={'success0':10000}),
                  dict(valid,samplingDesign='fixed-allocation')]:
    try:
        compare_import(malformed)
    except ValueError:
        pass
    else:
        raise AssertionError('Invalid import accepted')
for args in [('101','50'),('50','-1'),('x','50')]:
    rejected=subprocess.run([str(EXE),*args],capture_output=True,text=True)
    assert rejected.returncode==2 and not rejected.stdout

audit=subprocess.run(['/Users/panic/.elan/bin/lake','env','lean','-DwarningAsError=true','Audit.lean'],
                     cwd=ROOT,capture_output=True,text=True,check=True,timeout=30)
assert 'sorryAx' not in audit.stdout and 'error:' not in audit.stdout
(ROOT/'verification').mkdir(exist_ok=True)
(ROOT/'verification/axioms.log').write_text(audit.stdout)
report={'status':'PASS','leanTheoremsAdded':17,'parameterPairs':count,
        'exactClassicalAgreement':True,'quantumMaxAbsoluteError':max_error,
        'controlledRyDecompositionsChecked':101,
        'seedReproducibility':True,'zeroSuccessPosteriorAbsent':True,
        'importValidation':True,'hardwareExecuted':False,
        'sourceHashes':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in [ROOT/'ER01/Core.lean',ROOT/'ER01/Instrument.lean',
                                  ROOT/'InstrumentMain.lean',ROOT/'physics.py',ROOT/'ER01/InterfaceGraph.lean',ROOT/'graph.js']}}
(ROOT/'verification/report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
