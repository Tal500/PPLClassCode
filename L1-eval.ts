// L1-eval.ts

import * as assert from "assert";
import { filter, map, reduce } from "ramda";
import { first, isEmpty, rest } from "./L1-ast";
import { CExp, Exp, PrimOp, Program } from "./L1-ast";
import { hasError, isAppExp, isBoolExp, isCExp, isDefineExp, isError, isNumExp, isPrimOp,
         isProgram, isVarRef } from "./L1-ast";
import { parseL1 } from "./L1-ast";

// ========================================================
// Value type definition
export type Value = number | boolean | PrimOp | Error;

// ========================================================
// Environment data type
export type Env = EmptyEnv | NonEmptyEnv;
export interface EmptyEnv {tag: "EmptyEnv" };
export interface NonEmptyEnv {
    tag: "Env",
    var: string,
    val: Value,
    nextEnv: Env
};
const makeEmptyEnv = (): EmptyEnv => ({tag: "EmptyEnv"});
const makeEnv = (v: string, val: Value, env: Env): NonEmptyEnv =>
    ({tag: "Env", var: v, val: val, nextEnv: env});
const isEmptyEnv = (x: any): x is EmptyEnv => x.tag === "EmptyEnv";
const isNonEmptyEnv = (x: any): x is NonEmptyEnv => x.tag === "Env";
const isEnv = (x: any): x is Env => isEmptyEnv(x) || isNonEmptyEnv(x);

const applyEnv = (env: Env, v: string): Value =>
    isEmptyEnv(env) ? Error("var not found " + v) :
    env.var === v ? env.val :
    applyEnv(env.nextEnv, v);

// ========================================================
// Eval functions

const L1applicativeEval = (exp: CExp, env: Env): Value =>
    isError(exp)  ? exp :
    isNumExp(exp) ? exp.val :
    isBoolExp(exp) ? exp.val :
    isPrimOp(exp) ? exp :
    isVarRef(exp) ? applyEnv(env, exp.var) :
    isAppExp(exp) ? L1applyProcedure(exp.rator,
                                     map((rand) => L1applicativeEval(rand, env),
                                     exp.rands)) :
    Error("Bad L1 AST " + exp)

const L1applyProcedure = (proc: CExp, args: Value[]): Value =>
    hasError(args) ? Error("Bad argument: " + JSON.stringify(first(filter(isError, args)))) :
    isPrimOp(proc) ? applyPrimitive(proc, args) :
    Error("Bad procedure " + proc)

// @Pre: none of the args is an Error (checked in applyProcedure)
// @@There are type errors which we will address in L3
const applyPrimitive = (proc: PrimOp, args: Value[]): Value =>
    // @ts-ignore: the rhs of an arithmetic operation must be a number
    proc.op === "+" ? reduce((x, y) => x + y, 0, args) :
    // @ts-ignore: the rhs of an arithmetic operation must be a number
    proc.op === "-" ? reduce((x, y) => x - y, 0, args) :
    // @ts-ignore: the rhs of an arithmetic operation must be a number
    proc.op === "*" ? reduce((x, y) => x * y, 1, args) :
    // @ts-ignore: the rhs of an arithmetic operation must be a number
    proc.op === "/" ? reduce((x, y) => x / y, 1, args) :
    proc.op === ">" ? args[0] > args[1] :
    proc.op === "<" ? args[0] < args[1] :
    proc.op === "=" ? args[0] === args[1] :
    proc.op === "not" ? !args[0] :
    Error("Bad primitive op " + proc.op);

// Evaluate a sequence of expressions (in a program)
const evalExps = (exps: Exp[], env: Env): Value =>
    isEmpty(exps) ? Error("Empty program") :
    isDefineExp(first(exps)) ? evalDefineExps(exps, env) :
    isEmpty(rest(exps)) ? L1applicativeEval(first(exps), env) :
    isError(L1applicativeEval(first(exps), env)) ? Error("error") :
    evalExps(rest(exps), env);

// Eval a sequence of expressions when the first exp is a Define.
// Compute the rhs of the define, extend the env with the new binding
// then compute the rest of the exps in the new env.
const evalDefineExps = (exps: Exp[], env): Value => {
    let def = first(exps),
        rhs = L1applicativeEval(def.val, env),
        newEnv = makeEnv(def.var.var, rhs, env);
    return evalExps(rest(exps), newEnv);
}

// Main program
export const evalL1program = (program: Program): Value =>
    evalExps(program.exps, makeEmptyEnv());


// ========================================================
// Example
const p1 = parseL1("(L1 (define x 3) (+ (* x x) (+ x x)))");
if (isProgram(p1)) {
    // console.log("P1 = "+ JSON.stringify(p1));
    assert.equal(evalL1program(p1), 15);
}

const env1 = makeEnv("x", 1, makeEmptyEnv());
const e1 = parseL1("(+ x 2)");
if (isCExp(e1) && isEnv(env1)) {
    assert.equal(evalExps([e1], env1), 3);
}

