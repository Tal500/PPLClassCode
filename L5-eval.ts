// L5-eval-box

import { filter, map, reduce, repeat, zip, zipWith } from "ramda";
import { AppExp, CompoundExp, CExp, DefineExp, Exp, IfExp, LetrecExp, LetExp,
         Parsed, ProcExp, Program, SetExp } from './L5-ast';
import { AtomicExp, BoolExp, LitExp, NumExp, PrimOp, StrExp, VarDecl, VarRef } from "./L5-ast";
import { isBoolExp, isLitExp, isNumExp, isPrimOp, isStrExp, isVarRef } from "./L5-ast";
import { makeAppExp, makeBoolExp, makeIfExp, makeLitExp, makeNumExp, makeProcExp, makeStrExp,
         makeVarDecl, makeVarRef } from "./L5-ast";
import { parse } from "./L5-ast";
import { isArray, isBoolean, isEmpty, isNumber, isString } from "./L5-ast";
import { isAppExp, isCExp, isDefineExp, isExp, isIfExp, isLetrecExp, isLetExp,
         isProcExp, isProgram, isSetExp } from "./L5-ast";
import { applyEnv, applyEnvBdg, globalEnvAddBinding, makeExtEnv, setFBinding,
         theGlobalEnv, Env } from "./L5-env";
import { isEmptySExp, isSymbolSExp, makeEmptySExp, makeSymbolSExp } from './L5-value';
import { isClosure, isCompoundSExp, isSExp, makeClosure, makeCompoundSExp,
         Closure, CompoundSExp, SExp, Value } from "./L5-value";
import { getErrorMessages, hasNoError, isError }  from "./error";
import { allT, first, rest, second } from './list';

// ========================================================
// Eval functions

export const applicativeEval = (exp: CExp | Error, env: Env): Value | Error =>
    isError(exp)  ? exp :
    isNumExp(exp) ? exp.val :
    isBoolExp(exp) ? exp.val :
    isStrExp(exp) ? exp.val :
    isPrimOp(exp) ? exp :
    isVarRef(exp) ? applyEnv(env, exp.var) :
    isLitExp(exp) ? exp.val :
    isIfExp(exp) ? evalIf(exp, env) :
    isProcExp(exp) ? evalProc(exp, env) :
    isLetExp(exp) ? evalLet(exp, env) :
    isLetrecExp(exp) ? evalLetrec(exp, env) :
    isSetExp(exp) ? evalSet(exp, env) :
    isAppExp(exp) ? applyProcedure(applicativeEval(exp.rator, env),
                                   map((rand) => applicativeEval(rand, env), exp.rands)) :
    Error(`Bad L5 AST ${exp}`);

export const isTrueValue = (x: Value | Error): boolean | Error =>
    isError(x) ? x :
    ! (x === false);

const evalIf = (exp: IfExp, env: Env): Value | Error => {
    const test = applicativeEval(exp.test, env);
    return isError(test) ? test :
        isTrueValue(test) ? applicativeEval(exp.then, env) :
        applicativeEval(exp.alt, env);
};

const evalProc = (exp: ProcExp, env: Env): Closure =>
    makeClosure(exp.args, exp.body, env);

// @Pre: none of the args is an Error (checked in applyProcedure)
// KEY: This procedure does NOT have an env parameter.
//      Instead we use the env of the closure.
const applyProcedure = (proc: Value | Error, args: Array<Value | Error>): Value | Error =>
    isError(proc) ? proc :
    !hasNoError(args) ? Error(`Bad argument: ${getErrorMessages(args)}`) :
    isPrimOp(proc) ? applyPrimitive(proc, args) :
    isClosure(proc) ? applyClosure(proc, args) :
    Error(`Bad procedure ${JSON.stringify(proc)}`);

const applyClosure = (proc: Closure, args: Value[]): Value | Error => {
    let vars = map((v: VarDecl) => v.var, proc.params);
    return evalExps(proc.body, makeExtEnv(vars, args, proc.env));
}

// Evaluate a sequence of expressions (in a program)
export const evalExps = (exps: Exp[], env: Env): Value | Error =>
    isEmpty(exps) ? Error("Empty program") :
    isDefineExp(first(exps)) ? evalDefineExps(exps) :
    isEmpty(rest(exps)) ? applicativeEval(first(exps), env) :
    isError(applicativeEval(first(exps), env)) ? Error("error") :
    evalExps(rest(exps), env);

// L4-BOX @@
// define always updates theGlobalEnv
// We also only expect defineExps at the top level.
const evalDefineExps = (exps: Exp[]): Value | Error => {
    let def = first(exps);
    let rhs = applicativeEval(def.val, theGlobalEnv);
    if (isError(rhs))
        return rhs;
    else {
        globalEnvAddBinding(def.var.var, rhs);
        return evalExps(rest(exps), theGlobalEnv);
    }
}

// LET: Direct evaluation rule without syntax expansion
// compute the values, extend the env, eval the body.
const evalLet = (exp: LetExp, env: Env): Value | Error => {
    const vals = map((v) => applicativeEval(v, env), map((b) => b.val, exp.bindings));
    const vars = map((b) => b.var.var, exp.bindings);
    if (hasNoError(vals)) {
        return evalExps(exp.body, makeExtEnv(vars, vals, env));
    } else {
        return Error(getErrorMessages(vals));
    }
}

// LETREC: Direct evaluation rule without syntax expansion
// 1. extend the env with vars initialized to void (temporary value)
// 2. compute the vals in the new extended env
// 3. update the bindings of the vars to the computed vals
// 4. compute body in extended env
const evalLetrec = (exp: LetrecExp, env: Env): Value | Error => {
    const vars = map((b) => b.var.var, exp.bindings);
    const vals = map((b) => b.val, exp.bindings);
    const extEnv = makeExtEnv(vars, repeat(undefined, vars.length), env);
    // @@ Compute the vals in the extended env
    const cvals = map((v) => applicativeEval(v, extEnv), vals);
    if (hasNoError(cvals)) {
        // Bind vars in extEnv to the new values
        zipWith((bdg, cval) => setFBinding(bdg, cval), extEnv.frame.fbindings, cvals);
        return evalExps(exp.body, extEnv);
    } else {
        return Error(getErrorMessages(cvals));
    }
};

// L4-eval-box: Handling of mutation with set!
const evalSet = (exp: SetExp, env: Env): Value | Error => {
    const v = exp.var.var;
    const val = applicativeEval(exp.val, env);
    if (isError(val))
        return val;
    else {
        const bdg = applyEnvBdg(env, v);
        if (isError(bdg)) {
            return Error(`Var not found ${v}`)
        } else {
            setFBinding(bdg, val);
            return undefined;
        }
    }
};

// ========================================================
// Primitives

// @Pre: none of the args is an Error (checked in applyProcedure)
export const applyPrimitive = (proc: PrimOp, args: Value[]): Value | Error =>
    proc.op === "+" ? (allT(isNumber, args) ? reduce((x, y) => x + y, 0, args) : Error("+ expects numbers only")) :
    proc.op === "-" ? minusPrim(args) :
    proc.op === "*" ? (allT(isNumber, args) ? reduce((x, y) => x * y, 1, args) : Error("* expects numbers only")) :
    proc.op === "/" ? divPrim(args) :
    proc.op === ">" ? args[0] > args[1] :
    proc.op === "<" ? args[0] < args[1] :
    proc.op === "=" ? args[0] === args[1] :
    proc.op === "not" ? ! args[0] :
    proc.op === "eq?" ? eqPrim(args) :
    proc.op === "string=?" ? args[0] === args[1] :
    proc.op === "cons" ? consPrim(args[0], args[1]) :
    proc.op === "car" ? carPrim(args[0]) :
    proc.op === "cdr" ? cdrPrim(args[0]) :
    proc.op === "list?" ? isListPrim(args[0]) :
    proc.op === "number?" ? typeof(args[0]) === 'number' :
    proc.op === "boolean?" ? typeof(args[0]) === 'boolean' :
    proc.op === "symbol?" ? isSymbolSExp(args[0]) :
    proc.op === "string?" ? isString(args[0]) :
    // display, newline
    Error("Bad primitive op " + proc.op);

const minusPrim = (args: Value[]): number | Error => {
    // TODO complete
    let x = args[0], y = args[1];
    if (isNumber(x) && isNumber(y)) {
        return x - y;
    } else {
        return Error(`Type error: - expects numbers ${args}`)
    }
}

const divPrim = (args: Value[]): number | Error => {
    // TODO complete
    let x = args[0], y = args[1];
    if (isNumber(x) && isNumber(y)) {
        return x / y;
    } else {
        return Error(`Type error: / expects numbers ${args}`)
    }
}

const eqPrim = (args: Value[]): boolean | Error => {
    let x = args[0], y = args[1];
    if (isSymbolSExp(x) && isSymbolSExp(y)) {
        return x.val === y.val;
    } else if (isEmptySExp(x) && isEmptySExp(y)) {
        return true;
    } else if (isNumber(x) && isNumber(y)) {
        return x === y;
    } else if (isString(x) && isString(y)) {
        return x === y;
    } else if (isBoolean(x) && isBoolean(y)) {
        return x === y;
    } else {
        return false;
    }
}

const carPrim = (v: Value): Value | Error =>
    isCompoundSExp(v) ? first(v.val) :
    Error(`Car: param is not compound ${v}`);

const cdrPrim = (v: Value): Value | Error =>
    isCompoundSExp(v) ?
        ((v.val.length > 1) ? makeCompoundSExp(rest(v.val)) : makeEmptySExp()) :
    Error(`Cdr: param is not compound ${v}`);

const consPrim = (v: Value, lv: Value): CompoundSExp | Error =>
    isEmptySExp(lv) ? makeCompoundSExp([v]) :
    isCompoundSExp(lv) ? makeCompoundSExp([v].concat(lv.val)) :
    Error(`Cons: 2nd param is not empty or compound ${lv}`);

const isListPrim = (v: Value): boolean =>
    isEmptySExp(v) || isCompoundSExp(v);


// Main program
export const evalProgram = (program: Program): Value | Error =>
    evalExps(program.exps, theGlobalEnv);

export const evalParse = (s: string): Value | Error => {
    let ast: Parsed | Error = parse(s);
    if (isProgram(ast)) {
        return evalProgram(ast);
    } else if (isExp(ast)) {
        return evalExps([ast], theGlobalEnv);
    } else {
        return ast;
    }
}
