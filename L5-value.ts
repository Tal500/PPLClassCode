// ========================================================
// Value type definition for L5

import { isPrimOp, CExp, PrimOp, VarDecl } from './L5-ast';
import { Env } from './L5-env';

export type Value = SExp;

export type Functional = PrimOp | Closure;
export const isFunctional = (x: any): x is Functional => isPrimOp(x) || isClosure(x);

// ========================================================
// Closure for L5
export interface Closure {
    tag: "Closure";
    params: VarDecl[];
    body: CExp[];
    env: Env;
};
export const makeClosure = (params: VarDecl[], body: CExp[], env: Env): Closure =>
    ({tag: "Closure", params: params, body: body, env: env});
export const isClosure = (x: any): x is Closure => x.tag === "Closure";

// ========================================================
// SExp
export interface CompoundSExp {
    tag: "CompoundSexp";
    val: SExp[];
};
export interface EmptySExp {
    tag: "EmptySExp";
};
export interface SymbolSExp {
    tag: "SymbolSExp";
    val: string;
};

export type SExp = number | boolean | string | PrimOp | Closure | SymbolSExp | EmptySExp | CompoundSExp;
export const isSExp = (x: any): x is SExp =>
    typeof(x) === 'string' || typeof(x) === 'boolean' || typeof(x) === 'number' ||
    isSymbolSExp(x) || isCompoundSExp(x) || isEmptySExp(x) || isPrimOp(x) || isClosure(x);

export const makeCompoundSExp = (val: SExp[]): CompoundSExp =>
    ({tag: "CompoundSexp", val: val});
export const isCompoundSExp = (x: any): x is CompoundSExp => x.tag === "CompoundSexp";

export const makeEmptySExp = (): EmptySExp => ({tag: "EmptySExp"});
export const isEmptySExp = (x: any): x is EmptySExp => x.tag === "EmptySExp";

export const makeSymbolSExp = (val: string): SymbolSExp =>
    ({tag: "SymbolSExp", val: val});
export const isSymbolSExp = (x: any): x is SymbolSExp => x.tag === "SymbolSExp";
