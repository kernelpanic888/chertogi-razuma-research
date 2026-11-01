from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from urllib.parse import urlsplit, parse_qs
from functools import lru_cache
import json, subprocess
ROOT=Path(__file__).resolve().parent
EXE=ROOT.parent/'.lake/build/bin/er01'
@lru_cache(maxsize=128)
def run(p,l,mode):
 r=subprocess.run([str(EXE),str(p),'100',str(l),'100','4',mode],capture_output=True,text=True,timeout=5)
 if r.returncode: raise ValueError('Lean rejected parameters')
 data=json.loads(r.stdout)
 if data.get('schema')!='ER01/1': raise ValueError('Unexpected schema')
 return r.stdout.encode()
class Handler(BaseHTTPRequestHandler):
 def do_GET(self):
  u=urlsplit(self.path)
  try:
   if u.path in ('/','/index.html'):
    body=(ROOT/'index.html').read_bytes();kind='text/html; charset=utf-8'
   elif u.path=='/api/trace':
    q=parse_qs(u.query,strict_parsing=True)
    if set(q)!={'p','lambda','mode'} or any(len(v)!=1 for v in q.values()):raise ValueError('Invalid parameters')
    p=int(q['p'][0]);l=int(q['lambda'][0]);mode=q['mode'][0]
    if not 0<=p<=100 or not 0<=l<=100 or mode not in ('coarse','resolved'):raise ValueError('Invalid parameters')
    body=run(p,l,mode);kind='application/json'
   else:self.send_error(404);return
   self.send_response(200);self.send_header('Content-Type',kind);self.send_header('Cache-Control','no-store');self.send_header('X-Content-Type-Options','nosniff');self.end_headers();self.wfile.write(body)
  except (ValueError,subprocess.SubprocessError) as e:
   self.send_error(400,str(e))
if __name__=='__main__':
 if not EXE.is_file():raise SystemExit('Build first: lake build')
 print('ER-01 live Lean visual: http://127.0.0.1:4186',flush=True)
 ThreadingHTTPServer(('127.0.0.1',4186),Handler).serve_forever()
