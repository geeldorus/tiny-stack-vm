// Tiny stack VM for make.fun tiny-stack-vm-01.
// Implements ISA.md exactly, following the reference VM's step order:
// step limit, pc range, unknown opcode, truncated immediate, then the
// generic stack checks, then the instruction's own traps and effect.
// A trapping instruction writes nothing and keeps earlier output.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [opcode, immediate bytes, values popped, values pushed]
const OPS = [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2],
  [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3],
  [16, 0, 2, 1], [17, 0, 2, 1], [18, 0, 2, 1], [19, 0, 2, 1], [20, 0, 2, 1],
  [21, 0, 2, 1], [22, 0, 2, 1], [23, 0, 1, 1], [24, 0, 2, 1], [25, 0, 2, 1],
  [26, 0, 2, 1], [27, 0, 1, 1], [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1],
  [32, 0, 2, 1], [33, 0, 2, 1], [34, 0, 2, 1],
  [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0], [52, 0, 0, 0],
  [64, 0, 1, 1], [65, 0, 2, 0],
  [80, 0, 1, 0], [81, 0, 1, 0], [82, 0, 0, 1], [83, 0, 1, 0],
];
const IMM = new Uint8Array(256);
const NPOP = new Uint8Array(256);
const NPUSH = new Uint8Array(256);
const KNOWN = new Uint8Array(256);
for (const [o, i, a, b] of OPS) { IMM[o] = i; NPOP[o] = a; NPUSH[o] = b; KNOWN[o] = 1; }

function run(p: Uint8Array, inp: Uint8Array): { o: Uint8Array; c: number } {
  const S = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let cp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0;
  let ip = 0;
  let pc = 0;
  let st = 0;
  const end = (c: number) => ({ o: out.slice(0, ol), c });
  for (;;) {
    if (st === 1000000) return end(10);
    if (pc < 0 || pc >= p.length) return end(9);
    const op = p[pc];
    if (!KNOWN[op]) return end(5);
    const im = IMM[op];
    const pops = NPOP[op];
    const push = NPUSH[op];
    if (pc + im >= p.length) return end(9);
    st++;
    const nx = pc + 1 + im;
    if (sp < pops) return end(2);
    if (sp - pops + push > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0: return end(0);
      case 1: S[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 2: S[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 3: sp--; break;
      case 4: S[sp] = S[sp - 1]; sp++; break;
      case 5: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; }
      case 6: S[sp] = S[sp - 2]; sp++; break;
      case 7: { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break; }
      case 23: S[sp - 1] = -S[sp - 1] | 0; break;
      case 27: S[sp - 1] = ~S[sp - 1]; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
        const b = S[sp - 1];
        const a = S[sp - 2];
        if ((op >= 19 && op <= 22) && b === 0) return end(4);
        let r = 0;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        else if (op === 20) r = b === -1 ? 0 : (a % b) | 0;
        else if (op === 21) r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        else if (op === 22) r = ((a >>> 0) % (b >>> 0)) | 0;
        else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        S[sp++] = r;
        break;
      }
      case 48: case 49: case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        if (op === 48) { pc = nx + rel; break; }
        const v = S[--sp];
        if ((op === 49) === (v === 0)) pc = nx + rel;
        break;
      }
      case 51:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 64: {
        const ad = S[sp - 1];
        if (ad < 0 || ad > 255) return end(6);
        S[sp - 1] = M[ad];
        break;
      }
      case 65: {
        const ad = S[sp - 1];
        const v = S[sp - 2];
        if (ad < 0 || ad > 255) return end(6);
        sp -= 2;
        M[ad] = v;
        break;
      }
      case 80: {
        const s = String(S[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 81:
        if (ol >= 65536) return end(11);
        out[ol++] = S[--sp] & 255;
        break;
      case 82: S[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 83: return end(S[--sp] & 255);
      default: return end(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), r.c + '\n');
}
