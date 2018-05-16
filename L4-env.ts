// Environment for L4 (support for Letrec)
// =======================================
// An environment represents a partial function from symbols (variable names) to values.
// It supports the operation: apply-env(env,var)
// which either returns the value of var in the environment, or else throws an error.
//
// Env is defined inductively by the following cases:
// * <env> ::= <empty-env> | <extended-env> | <rec-env>
// * <empty-env> ::= (empty-env) // empty-env()
// * <extended-env> ::= (env (symbol+) (value+) next-env) // env(vars:List(Symbol), vals:List(Value), next-env: Env)
// * <rec-ext-env> ::= (rec-env (symbol+) (params+) (bodies+) next-env)
//       // rec-env(vars:List(Symbol), paramss:List(List(var-decl)), bodiess:List(List(cexp)), next-env: Env)
//
// The key operation on env is apply-env(var) which returns the value associated to var in env
// or throw an error if var is not defined in env.

import { VarDecl } from './L3-ast';
import { CExp4 } from './L4-ast';
import { makeClosure4, Value4 } from './L4-value';

// ========================================================
// Environment data type
export type Env = EmptyEnv | ExtEnv | RecEnv;
export interface EmptyEnv {tag: "EmptyEnv" };
export interface ExtEnv {
    tag: "ExtEnv";
    vars: string[];
    vals: Value4[];
    nextEnv: Env;
};
export interface RecEnv {
    tag: "RecEnv";
    vars: string[];
    paramss: VarDecl[][];
    bodiess: CExp4[][];
    nextEnv: Env;
};

export const makeEmptyEnv = (): EmptyEnv => ({tag: "EmptyEnv"});
export const makeExtEnv = (vs: string[], vals: Value4[], env: Env): ExtEnv =>
    ({tag: "ExtEnv", vars: vs, vals: vals, nextEnv: env});
export const makeRecEnv = (vs: string[], paramss: VarDecl[][], bodiess: CExp4[][], env: Env): RecEnv =>
    ({tag: "RecEnv", vars: vs, paramss: paramss, bodiess: bodiess, nextEnv: env});

const isEmptyEnv = (x: any): x is EmptyEnv => x.tag === "EmptyEnv";
const isExtEnv = (x: any): x is ExtEnv => x.tag === "ExtEnv";
const isRecEnv = (x: any): x is RecEnv => x.tag === "RecEnv";

const isEnv = (x: any): x is Env => isEmptyEnv(x) || isExtEnv(x) || isRecEnv(x);

// Apply-env
export const applyEnv = (env: Env, v: string): Value4 | Error =>
    isEmptyEnv(env) ? Error(`var not found ${v}`) :
    isExtEnv(env) ? applyExtEnv(env, v) :
    applyRecEnv(env, v);

const applyExtEnv = (env: ExtEnv, v: string): Value4 | Error =>
    env.vars.includes(v) ? env.vals[env.vars.indexOf(v)] :
    applyEnv(env.nextEnv, v);

const applyRecEnv = (env: RecEnv, v: string): Value4 | Error =>
    env.vars.includes(v) ? makeClosure4(env.paramss[env.vars.indexOf(v)],
                                        env.bodiess[env.vars.indexOf(v)],
                                        env) :
    applyEnv(env.nextEnv, v);
