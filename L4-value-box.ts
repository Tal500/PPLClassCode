// ========================================================
// L4-value-box: Value type definition for L4-eval-box
// Changes wrt L4-value:
// 1. refer to L4-env-box in Closure4
// 2. introduce void value type

import { isPrimOp, PrimOp, VarDecl } from './L3-ast';
import { isEmptySExp, isSymbolSExp, makeEmptySExp, makeSymbolSExp, EmptySExp, SymbolSExp } from './L3-value';
import { CExp4 } from './L4-ast-box';
import { Env } from './L4-env-box';

// Add void for value of side-effect expressions - set! and define
export type Value4 = SExp4 | Closure4 | undefined;

export type Functional = PrimOp | Closure4;
export const isFunctional = (x: any): x is Functional => isPrimOp(x) || isClosure4(x);

// ========================================================
// Closure for L4 - the field env is added.
// We also use a frame-based representation of closures as opposed to one env per var.
export interface Closure4 {
    tag: "Closure4";
    params: VarDecl[];
    body: CExp4[];
    env: Env;
};
export const makeClosure4 = (params: VarDecl[], body: CExp4[], env: Env): Closure4 =>
    ({tag: "Closure4", params: params, body: body, env: env});
export const isClosure4 = (x: any): x is Closure4 => x.tag === "Closure4";

// ========================================================
// SExp
export interface CompoundSExp4 {
    tag: "CompoundSexp4";
    val: SExp4[];
};

export type SExp4 = number | boolean | string | PrimOp | Closure4 | SymbolSExp | EmptySExp | CompoundSExp4;
export const isSExp4 = (x: any): x is SExp4 =>
    typeof(x) === 'string' || typeof(x) === 'boolean' || typeof(x) === 'number' ||
    isSymbolSExp(x) || isCompoundSExp4(x) || isEmptySExp(x) || isPrimOp(x) || isClosure4(x);

export const makeCompoundSExp4 = (val: SExp4[]): CompoundSExp4 =>
    ({tag: "CompoundSexp4", val: val});
export const isCompoundSExp4 = (x: any): x is CompoundSExp4 => x.tag === "CompoundSexp4";
