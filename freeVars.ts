import { any as some } from "ramda";
import { apply, map, reduce, union } from "ramda";
import { Parsed, VarRef } from "./L3-ast";
import { isAppExp, isAtomicExp, isBoolExp, isDefineExp, isIfExp, isLetExp, isLitExp, isNumExp,
         isPrimOp, isProcExp, isProgram, isStrExp, isVarRef } from './L3-ast';

// TODO: No error handling
export const height = (exp: Parsed | Error): number =>
    isAtomicExp(exp) ? 1 :
    isLitExp(exp) ? 1 :
    isDefineExp(exp) ? 1 + height(exp.val) :
    isIfExp(exp) ? 1 + Math.max(height(exp.test), height(exp.then), height(exp.alt)) :
    isProcExp(exp) ? 1 + reduce(Math.max, 0,
                                map((bodyExp) => height(bodyExp), exp.body)) :
    isLetExp(exp) ? 1 + Math.max(
                            reduce(Math.max, 0,
                                   map((binding) => height(binding.val), exp.bindings)),
                            reduce(Math.max, 0,
                                   map((bodyExp) => height(bodyExp), exp.body))) :
    isAppExp(exp) ? Math.max(height(exp.rator),
                             reduce(Math.max, 0,
                                    map((rand) => height(rand), exp.rands))) :
    isProgram(exp) ? 1 + reduce(Math.max, 0,
                                map((e) => height(e), exp.exps)) :
    -1;

export const occursFree = (v: string, e: Parsed | Error): boolean =>
    isBoolExp(e) ? false :
    isNumExp(e) ? false :
    isStrExp(e) ? false :
    isLitExp(e) ? false :
    isVarRef(e) ? (v === e.var) :
    isIfExp(e) ? occursFree(v, e.test) || occursFree(v, e.then) || occursFree(v, e.alt) :
    isProcExp(e) ? ! (map((p) => p.var, e.args).includes(v)) &&
                   some((b) => occursFree(v, b), e.body) :
    isPrimOp(e) ? false :
    isAppExp(e) ? occursFree(v, e.rator) ||
                  some((rand) => occursFree(v, rand), e.rands) :
    isDefineExp(e) ? (v !== e.var.var) && occursFree(v, e.val) :
    isLetExp(e) ? false : // TODO
    isProgram(e) ? false : // TODO
    false;

export const referencedVars = (e: Parsed | Error): ReadonlyArray<VarRef> =>
    isBoolExp(e) ? [] :
    isNumExp(e) ? [] :
    isStrExp(e) ? [] :
    isLitExp(e) ? [] :
    isPrimOp(e) ? [] :
    isVarRef(e) ? [e] :
    // @ts-ignore: Expected 1-2 arguments, but got 3.
    isIfExp(e) ? union(referencedVars(e.test), referencedVars(e.then), referencedVars(e.alt)) :
    isAppExp(e) ? union(referencedVars(e.rator),
                        reduce(union, [], map(referencedVars, e.rands))) :
    isProcExp(e) ? reduce(union, [], map(referencedVars, e.body)) :
    isDefineExp(e) ? referencedVars(e.val) :
    isProgram(e) ? reduce(union, [], map(referencedVars, e.exps)) :
    isLetExp(e) ? [] : // TODO
    [];
