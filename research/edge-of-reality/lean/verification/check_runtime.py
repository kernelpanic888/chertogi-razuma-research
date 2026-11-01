from pathlib import Path
from fractions import Fraction
import subprocess,json
root=Path(__file__).resolve().parents[1];exe=root/'.lake/build/bin/er01'
def run(args):
 r=subprocess.run([str(exe),*map(str,args)],capture_output=True,text=True)
 assert r.returncode==0,r.stderr
 return json.loads(r.stdout)
count=0
for q in range(1,9):
 for d in range(1,9):
  for p in range(q+1):
   for l in range(d+1):
    for mode in ('coarse','resolved'):
     r=run([p,q,l,d,6,mode]);a=p*d*d;b=l*l*(q-p);w=a+b
     assert Fraction(**dict(numerator=r['successWeight']['numerator'],denominator=r['successWeight']['denominator']))==Fraction(p,q)+Fraction(l,d)**2*(1-Fraction(p,q))
     assert 0<=Fraction(w,q*d*d)<=1
     tr=r['trace'];assert len(tr)==7
     assert tr[0]['phase']=='prepared' and tr[1]['phase']=='filtered'
     assert [t['tick'] for t in tr]==sorted(t['tick'] for t in tr)
     assert tr[4]==tr[5]==tr[6]
     assert all(t['mass']=={'zero':a,'one':b,'total':w} for t in tr[1:])
     if w==0:
      assert tr[2]['phase']=='rejected'
      assert all(t['readout'] is None and t['conditionalBranchZero'] is None for t in tr)
     else:
      assert [t['phase'] for t in tr[:5]]==['prepared','filtered','admitted','observed','returned']
      post=tr[4]['conditionalBranchZero'];assert Fraction(post['numerator'],post['denominator'])==Fraction(a,w)
      assert sum(x['mass'] for x in tr[4]['readout'])==w
      assert [x['label'] for x in tr[4]['readout']]==([0] if mode=='coarse' else [0,1])
      assert all(t['readout'] is None for t in tr[:3])
     count+=1
bad=[[],[1,0,1,2,4,'resolved'],[1,2,1,0,4,'resolved'],[3,2,1,2,4,'resolved'],[1,2,3,2,4,'resolved'],[1,2,1,2,1001,'resolved'],[1,2,1,2,4,'unknown'],['x',2,1,2,4,'resolved'],[1,1000001,1,2,4,'resolved']]
for args in bad:
 r=subprocess.run([str(exe),*map(str,args)],capture_output=True,text=True);assert r.returncode==2 and not r.stdout
for n in range(5):assert len(run([1,2,1,2,n,'resolved'])['trace'])==n+1
result={'status':'PASS','exactCases':count,'invalidInputsRejected':len(bad),'prefixLengthsChecked':5,'reference':'Python Fraction; independent exact arithmetic','checks':['mass budget','posterior','phase closure','terminal fixed point','tick monotonicity','readout separation','observation does not alter masses','no zero-weight normalization']}
(root/'verification/runtime.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
