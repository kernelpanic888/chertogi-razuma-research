import { readFile, writeFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

const abs = n => n < 0n ? -n : n;
const gcd = (a, b) => { a = abs(a); b = abs(b); while (b) [a, b] = [b, a % b]; return a; };
const rat = (n, d = 1n) => {
  if (d === 0n) throw new Error('zero denominator');
  if (d < 0n) { n = -n; d = -d; }
  const g = gcd(n, d);
  return { n: n / g, d: d / g };
};
const add = (a, b) => rat(a.n * b.d + b.n * a.d, a.d * b.d);
const sub = (a, b) => rat(a.n * b.d - b.n * a.d, a.d * b.d);
const mul = (a, b) => rat(a.n * b.n, a.d * b.d);
const inv = a => { if (a.n === 0n) return rat(0n); return rat(a.d, a.n); };
const sq = a => mul(a, a);
const absRat = a => rat(abs(a.n), a.d);
const renderRat = a => `${a.n}/${a.d}`;
const parseRat = text => {
  if (!/^-?\d+\/[1-9]\d*$/.test(text)) throw new Error(`noncanonical rational: ${text}`);
  const [n, d] = text.split('/').map(BigInt), value = rat(n, d);
  if (renderRat(value) !== text) throw new Error(`unreduced rational: ${text}`);
  return value;
};
const eq = (a, b) => a.n === b.n && a.d === b.d;

export function generatedRows(level, amplitude) {
  const N = BigInt(level + 2), denominator = BigInt(level + 1), total = 2n * N * N, rows = [];
  for (let nodeId = 0n; nodeId < total; nodeId++) {
    const hemisphere = nodeId >= N * N, local = nodeId % (N * N);
    const tIndex = local / N, vIndex = local % N;
    const t = add(rat(-1n), rat(2n * tIndex, denominator));
    const v = add(rat(-1n), rat(2n * vIndex, denominator));
    const sign = rat(hemisphere ? 1n : -1n);
    const x = mul(sign, mul(sub(rat(1n), sq(t)), inv(add(rat(1n), sq(t)))));
    const y = mul(mul(rat(2n), t), inv(add(rat(1n), sq(t))));
    const width = add(absRat(x), absRat(y));
    const slope = mul(v, width);
    const forward = add(sq(x), sq(add(y, mul(amplitude, slope))));
    const inverse = inv(forward);
    rows.push({ level, nodeId, hemisphere, tIndex, vIndex, t, v, x, y, slope, forward, inverse });
  }
  return rows;
}

const renderRow = row => [
  'ROW', row.level, row.nodeId, row.hemisphere ? 'E' : 'W', row.tIndex, row.vIndex,
  row.t, row.v, row.x, row.y, row.slope, row.forward, row.inverse, rat(0n), rat(0n),
].map((value, index) => index >= 6 ? renderRat(value) : String(value)).join('|');

export function generateDocument(level = 2, amplitude = rat(1n, 2n)) {
  const rows = generatedRows(level, amplitude);
  return [`IFBS31E|1|${level}|${renderRat(amplitude)}|${rows.length}`, ...rows.map(renderRow)].join('\n');
}

export function verifyDocument(text) {
  try {
    const lines = text.replace(/\r/g, '').split('\n');
    if (lines.at(-1) === '') lines.pop();
    const header = lines.shift()?.split('|') ?? [];
    if (header.length !== 5 || header[0] !== 'IFBS31E' || header[1] !== '1') throw new Error('bad header');
    const level = Number(header[2]);
    if (!Number.isSafeInteger(level) || level < 0 || String(level) !== header[2]) throw new Error('bad level');
    const amplitude = parseRat(header[3]), count = Number(header[4]), expected = generatedRows(level, amplitude);
    if (count !== expected.length || lines.length !== count) throw new Error('row count mismatch');
    const seen = new Set();
    for (let index = 0; index < lines.length; index++) {
      const fields = lines[index].split('|'), target = expected[index];
      if (fields.length !== 15 || fields[0] !== 'ROW') throw new Error(`bad row ${index}`);
      const [rowLevel, nodeId, hemisphere, tIndex, vIndex] = [Number(fields[1]), BigInt(fields[2]), fields[3], BigInt(fields[4]), BigInt(fields[5])];
      if (rowLevel !== level || nodeId !== target.nodeId || seen.has(fields[2])) throw new Error(`identity mismatch ${index}`);
      seen.add(fields[2]);
      if (hemisphere !== (target.hemisphere ? 'E' : 'W') || tIndex !== target.tIndex || vIndex !== target.vIndex) throw new Error(`index mismatch ${index}`);
      const actual = fields.slice(6).map(parseRat), wanted = [target.t, target.v, target.x, target.y, target.slope, target.forward, target.inverse, rat(0n), rat(0n)];
      if (!actual.every((value, i) => eq(value, wanted[i]))) throw new Error(`field mismatch ${index}`);
    }
    return { ok: true, schema: 'IFBS31E/1', level, rows: count, amplitude: renderRat(amplitude) };
  } catch (error) {
    return { ok: false, error: error.message };
  }
}

const main = async () => {
  const here = new URL('.', import.meta.url), fixture = new URL('fixture.ifbs', here);
  if (process.argv.includes('--write-fixture')) await writeFile(fixture, generateDocument(2) + '\n');
  const target = process.argv.slice(2).find(arg => !arg.startsWith('--'));
  const text = await readFile(target ?? fixture, 'utf8'), result = verifyDocument(text);
  console.log(JSON.stringify(result));
  if (!result.ok) process.exitCode = 1;
};

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) await main();
