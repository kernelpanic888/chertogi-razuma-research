"""Independent two-qubit density-matrix reference and classical control.

Only the diagonal input family is supported. No quantum advantage, hardware
execution, spacetime geometry or time-travel interpretation is inferred.
"""
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import json
import math
import random
import subprocess

ROOT = Path(__file__).resolve().parent
EXE = ROOT / '.lake/build/bin/instrument'
LABELS = ('success0', 'success1', 'failure0', 'failure1')


def integer(value, lo, hi, name):
    if type(value) is not int or not lo <= value <= hi:
        raise ValueError('%s must be an integer in %s..%s' % (name, lo, hi))
    return value


@lru_cache(maxsize=256)
def lean_prediction(p, lam):
    integer(p, 0, 100, 'pPercent')
    integer(lam, 0, 100, 'lambdaPercent')
    r = subprocess.run([str(EXE), str(p), str(lam)], capture_output=True,
                       text=True, timeout=5)
    if r.returncode:
        raise ValueError('Lean rejected parameters')
    data = json.loads(r.stdout)
    if data.get('schema') != 'ER01-INSTRUMENT/1':
        raise ValueError('Unexpected Lean output')
    return data


def classical_exact(p, lam):
    """Independent Bernoulli source and conditional acceptance, exact rationals."""
    source = Fraction(p, 100)
    transmission = Fraction(lam, 100) ** 2
    return (source, (1-source)*transmission, Fraction(0),
            (1-source)*(1-transmission))


def matmul(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def quantum_reference(p, lam):
    """U rho U^dagger for system + ancilla; basis |system,ancilla>.

    U is controlled Ry(2 acos(lambda)); ancilla starts in |0>.
    Measuring both qubits produces four joint Born probabilities.
    """
    source, amplitude = p/100, lam/100
    loss = math.sqrt(1-amplitude*amplitude)
    u = [[1,0,0,0], [0,1,0,0],
         [0,0,amplitude,-loss], [0,0,loss,amplitude]]
    rho = [[0.0]*4 for _ in range(4)]
    rho[0][0], rho[2][2] = source, 1-source
    dagger = [list(row) for row in zip(*u)]  # all entries are real here
    evolved = matmul(matmul(u, rho), dagger)
    return [evolved[i][i] for i in (0,2,1,3)]


def wilson(k, n):
    if not n:
        return None
    z = 1.959963984540054
    phat = k/n
    den = 1+z*z/n
    mid = (phat+z*z/(2*n))/den
    half = z*math.sqrt(phat*(1-phat)/n+z*z/(4*n*n))/den
    return [max(0, mid-half), min(1, mid+half)]


def summarize(counts, expected):
    total = sum(counts.values())
    accepted = counts['success0']+counts['success1']
    target = expected[0]+expected[1]
    return dict(shots=total, counts=counts, successRate=accepted/total,
                successInterval95=wilson(accepted,total),
                conditionalZero=counts['success0']/accepted if accepted else None,
                conditionalInterval95=wilson(counts['success0'],accepted),
                expectedCounts={k: total*v for k,v in zip(LABELS,expected)},
                expectedSuccess=target,
                expectedConditionalZero=expected[0]/target if target else None,
                impossibleOutcomeCounts=sum(counts[k] for k,v in zip(LABELS,expected)
                                            if v == 0))


def sample_quantum(probabilities, shots, seed):
    rng = random.Random(seed)
    counts = dict.fromkeys(LABELS,0)
    cutoffs = [sum(probabilities[:i+1]) for i in range(3)]
    for _ in range(shots):
        x = rng.random()
        i = next((i for i,c in enumerate(cutoffs) if x < c),3)
        counts[LABELS[i]] += 1
    return counts


def sample_classical(p, lam, shots, seed):
    rng = random.Random(seed)
    counts = dict.fromkeys(LABELS,0)
    for _ in range(shots):
        if rng.random() < p/100:
            counts['success0'] += 1
        elif rng.random() < (lam/100)**2:
            counts['success1'] += 1
        else:
            counts['failure1'] += 1
    return counts


def protocol(p, lam):
    theta = 2*math.acos(lam/100)
    header = ('OPENQASM 2.0;\ninclude "qelib1.inc";\n'
              'gate cry(theta) c,t { ry(theta/2) t; cx c,t; '
              'ry(-theta/2) t; cx c,t; }\n'
              'qreg q[2];\ncreg c[2];\n')
    tail = 'cry(%.17g) q[0],q[1];\nmeasure q[0] -> c[0];\nmeasure q[1] -> c[1];\n' % theta
    return dict(pPercent=p, lambdaPercent=lam, theta=theta,
                preparation='Randomly select preparation 0 with probability p/100 for each trial; otherwise preparation 1. Count every trial, including failures. Fixed shot allocations are a different sampling design.',
                preparation0=header+tail, preparation1=header+'x q[0];\n'+tail,
                bitstrings={'00':'success0','01':'success1','10':'failure0','11':'failure1'},
                bitOrder='c[1]c[0] = ancilla,system',
                status='Circuit specification only; not submitted to hardware')


def experiment(p, lam, shots, seed):
    integer(shots,1,100000,'shots')
    integer(seed,0,2147483647,'seed')
    lean = lean_prediction(p,lam)
    exact = classical_exact(p,lam)
    lp = [Fraction(m,lean['denominator']) for m in lean['masses']]
    qr = quantum_reference(p,lam)
    error = max(abs(float(a)-b) for a,b in zip(lp,qr))
    if tuple(lp) != exact or error > 1e-12:
        raise ValueError('Independent reference disagreement')
    ideal = list(map(float,lp))
    return dict(schema='ER01-PHYSICS/1',pPercent=p,lambdaPercent=lam,
                shots=shots,seed=seed,lean=lean,
                reference=dict(exactClassicalMatch=True,quantumMaxError=error,
                               probabilities=qr),
                quantum=summarize(sample_quantum(qr,shots,seed),ideal),
                classical=summarize(sample_classical(p,lam,shots,seed ^ 0x5a5a5a5a),ideal),
                protocol=protocol(p,lam),
                provenance='LOCAL_SIMULATION_NOT_HARDWARE')


def compare_import(data):
    if not isinstance(data,dict) or data.get('schema') != 'ER01-COUNTS/1':
        raise ValueError('Expected ER01-COUNTS/1 JSON')
    p = integer(data.get('pPercent'),0,100,'pPercent')
    lam = integer(data.get('lambdaPercent'),0,100,'lambdaPercent')
    counts = data.get('counts')
    if not isinstance(counts,dict) or set(counts) != set(LABELS):
        raise ValueError('Expected all four outcome counts')
    for k,v in counts.items():
        integer(v,0,1000000000,k)
    shots = integer(data.get('shots'),1,1000000000,'shots')
    if sum(counts.values()) != shots:
        raise ValueError('Counts must sum to shots, including failures')
    if data.get('samplingDesign') != 'iid-mixture':
        raise ValueError('This comparison requires iid-mixture sampling')
    lean = lean_prediction(p,lam)
    ideal = [m/lean['denominator'] for m in lean['masses']]
    return dict(schema='ER01-IMPORT-COMPARISON/1',pPercent=p,lambdaPercent=lam,
                summary=summarize(counts,ideal),
                provenance='USER_SUPPLIED_COUNTS_UNVERIFIED',
                source=str(data.get('source','unspecified'))[:160])
