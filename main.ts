// Tiny stack VM: a fresh interpreter of make.fun's tiny stack ISA v1.
// Node 22, no dependencies. Runs each /input/<id>/ program and writes
// /output/<id>/{stdout.bin,exit.txt}; arithmetic wraps at 32 bits.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode metadata: byte -> [immediate bytes, values popped, values pushed].
// A byte missing here is not an opcode and traps 5.
const META: Record<number, [number, number, number]> = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x10: [0, 2, 1], 0x11: [0, 2, 1], 0x12: [0, 2, 1], 0x13: [0, 2, 1],
  0x14: [0, 2, 1], 0x15: [0, 2, 1], 0x16: [0, 2, 1], 0x17: [0, 1, 1],
  0x18: [0, 2, 1], 0x19: [0, 2, 1], 0x1a: [0, 2, 1], 0x1b: [0, 1, 1],
  0x1c: [0, 2, 1], 0x1d: [0, 2, 1], 0x1e: [0, 2, 1], 0x20: [0, 2, 1],
  0x21: [0, 2, 1], 0x22: [0, 2, 1], 0x30: [2, 0, 0], 0x31: [2, 1, 0],
  0x32: [2, 1, 0], 0x33: [2, 0, 0], 0x34: [0, 0, 0], 0x40: [0, 1, 1],
  0x41: [0, 2, 0], 0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1],
  0x53: [0, 1, 0],
};

// Two-operand arithmetic. Returns undefined for division by zero (trap 4).
function calc(op: number, a: number, b: number): number | undefined {
  if (b === 0 && op >= 0x13 && op <= 0x16) return undefined; // DIV/MOD/DIVU/MODU by zero
  if (op === 0x10) return (a + b) | 0;
  if (op === 0x11) return (a - b) | 0;
  if (op === 0x12) return Math.imul(a, b); // exact low 32 bits
  if (op === 0x13) return a === -2147483648 && b === -1 ? a : (a / b) | 0; // truncated toward zero
  if (op === 0x14) return b === -1 ? 0 : (a % b) | 0; // sign of a
  if (op === 0x15) return Math.floor((a >>> 0) / (b >>> 0)) | 0; // unsigned
  if (op === 0x16) return ((a >>> 0) % (b >>> 0)) | 0; // unsigned
  if (op === 0x18) return a & b;
  if (op === 0x19) return a | b;
  if (op === 0x1a) return a ^ b;
  if (op === 0x1c) return a << (b & 31);
  if (op === 0x1d) return a >> (b & 31); // arithmetic shift
  if (op === 0x1e) return (a >>> (b & 31)) | 0; // logical shift
  if (op === 0x20) return a === b ? 1 : 0;
  if (op === 0x21) return a < b ? 1 : 0;
  return (a >>> 0) < (b >>> 0) ? 1 : 0; // 0x22 LTU, unsigned
}

const encoder = new TextEncoder();

function execute(prog: Uint8Array, input: Uint8Array): { bytes: Uint8Array; exit: number } {
  const stack = new Int32Array(256);
  let sp = 0;
  const calls = new Int32Array(64);
  let cp = 0;
  const mem = new Int32Array(256);
  const buf = new Uint8Array(65536);
  let outLen = 0;
  let inPos = 0;
  let pc = 0;
  let steps = 0;
  const finish = (code: number) => ({ bytes: buf.subarray(0, outLen), exit: code });
  while (true) {
    if (steps === 1000000) return finish(10);
    if (pc < 0 || pc >= prog.length) return finish(9);
    const op = prog[pc];
    const meta = META[op];
    if (meta === undefined) return finish(5);
    const [imm, need, give] = meta;
    if (pc + imm >= prog.length) return finish(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < need) return finish(2);
    if (sp - need + give > 256) return finish(3);
    pc = next;
    switch (op) {
      case 0x00: return finish(0);
      case 0x01: stack[sp++] = (prog[next - 1] << 24) >> 24; break; // sign-extended
      case 0x02: // little-endian signed
        stack[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: stack[sp] = stack[sp - 1]; sp++; break;
      case 0x05: { const x = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = x; break; }
      case 0x06: stack[sp] = stack[sp - 2]; sp++; break;
      case 0x07: { const x = stack[sp - 3]; stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = x; break; }
      case 0x17: stack[sp - 1] = -stack[sp - 1] | 0; break; // wraps at INT_MIN
      case 0x1b: stack[sp - 1] = ~stack[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const r = calc(op, stack[sp - 2], stack[sp - 1]);
        if (r === undefined) return finish(4);
        sp -= 2;
        stack[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = stack[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return finish(7);
        calls[cp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return finish(8);
        pc = calls[--cp];
        break;
      case 0x40: {
        const addr = stack[sp - 1];
        if (addr < 0 || addr >= 256) return finish(6);
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = stack[sp - 1];
        const v = stack[sp - 2];
        if (addr < 0 || addr >= 256) return finish(6);
        sp -= 2;
        mem[addr] = v;
        break;
      }
      case 0x50: { // decimal ASCII, no newline
        const bytes = encoder.encode(String(stack[sp - 1]));
        if (outLen + bytes.length > 65536) return finish(11); // writes nothing
        sp--;
        buf.set(bytes, outLen);
        outLen += bytes.length;
        break;
      }
      case 0x51:
        if (outLen + 1 > 65536) return finish(11);
        buf[outLen++] = stack[--sp] & 255;
        break;
      case 0x52: stack[sp++] = inPos < input.length ? input[inPos++] : -1; break;
      case 0x53: return finish(stack[--sp] & 255);
    }
  }
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN_DIR).sort()) {
  const r = execute(
    new Uint8Array(readFileSync(join(IN_DIR, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(IN_DIR, id, 'input.bin'))),
  );
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), r.bytes);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), `${r.exit}\n`);
}
