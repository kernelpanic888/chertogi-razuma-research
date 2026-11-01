from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlsplit, parse_qs
from pathlib import Path
import json
import subprocess
from threading import BoundedSemaphore
from physics import experiment, compare_import, EXE

ROOT = Path(__file__).resolve().parent
SLOTS = BoundedSemaphore(4)


class Handler(BaseHTTPRequestHandler):
    def reply(self, status, data, kind='application/json; charset=utf-8'):
        body = data if isinstance(data,bytes) else json.dumps(data,ensure_ascii=False).encode()
        self.send_response(status)
        self.send_header('Content-Type',kind)
        self.send_header('Content-Length',str(len(body)))
        self.send_header('Cache-Control','no-store')
        self.send_header('X-Content-Type-Options','nosniff')
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        u = urlsplit(self.path)
        if u.path in ('/','/index.html'):
            return self.reply(200,(ROOT/'index.html').read_bytes(),'text/html; charset=utf-8')
        if u.path == '/graph.js':
            return self.reply(200,(ROOT/'graph.js').read_bytes(),'text/javascript; charset=utf-8')
        if u.path != '/api/experiment':
            return self.reply(404,{'error':'Not found'})
        if not SLOTS.acquire(blocking=False):
            return self.reply(429,{'error':'Busy; retry shortly'})
        try:
            q = parse_qs(u.query,strict_parsing=True)
            if set(q) != {'p','lambda','shots','seed'} or any(len(v)!=1 for v in q.values()):
                raise ValueError('Expected p, lambda, shots, seed')
            data = experiment(*(int(q[k][0]) for k in ('p','lambda','shots','seed')))
            self.reply(200,data)
        except (ValueError,RuntimeError,subprocess.SubprocessError) as e:
            self.reply(400,{'error':str(e)})
        finally:
            SLOTS.release()

    def do_POST(self):
        if self.path != '/api/compare':
            return self.reply(404,{'error':'Not found'})
        try:
            length = int(self.headers.get('Content-Length','0'))
            if not 0 < length <= 32768:
                raise ValueError('JSON must be 1..32768 bytes')
            self.reply(200,compare_import(json.loads(self.rfile.read(length))))
        except (ValueError,TypeError) as e:
            self.reply(400,{'error':str(e)})


if __name__ == '__main__':
    if not EXE.is_file():
        raise SystemExit('Build first: lake build')
    print('ER-01 physics sandbox: http://127.0.0.1:4193',flush=True)
    ThreadingHTTPServer(('127.0.0.1',4193),Handler).serve_forever()
