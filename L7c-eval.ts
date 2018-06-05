// L7-eval: CPS version of L5 with concrete data-structure continuations

import { filter, map, reduce, repeat, zip, zipWith } from "ramda";
import { isArray, isBoolean, isEmpty, isNumber, isString } from "./L5-ast";
import { AtomicExp, BoolExp, LitExp, NumExp, PrimOp, StrExp, VarDecl, VarRef } from "./L5-ast";
import { isBoolExp, isLitExp, isNumExp, isPrimOp, isStrExp, isVarRef } from "./L5-ast";
import { makeAppExp, makeBoolExp, makeIfExp, makeLitExp, makeNumExp, makeProcExp, makeStrExp,
         makeVarDecl, makeVarRef } from "./L5-ast";
import { parse, unparse } from "./L5-ast";
import { makeProgram, AppExp, CompoundExp, CExp, DefineExp, Exp, IfExp, LetrecExp,
         LetExp, Parsed, ProcExp, Program, SetExp } from './L5-ast';
import { isAppExp, isCExp, isDefineExp, isExp, isIfExp, isLetrecExp, isLetExp,
         isProcExp, isProgram, isSetExp } from "./L5-ast";
import { applyEnv, applyEnvBdg, globalEnvAddBinding, makeExtEnv, setFBinding,
         theGlobalEnv, Env, ExtEnv } from "./L5-env";
import { isEmptySExp, isSymbolSExp, makeEmptySExp, makeSymbolSExp } from './L5-value';
import { isClosure, isCompoundSExp, isSExp, makeClosure, makeCompoundSExp,
         Closure, CompoundSExp, SExp, Value } from "./L5-value";
import { getErrorMessages, hasNoError, isError }  from "./error";
import { allT, first, rest, second } from './list';

// ========================================================
// Concrete Continuation datatype
// type Cont = (res: Value | Error) => Value | Error;
// type ContArray = (results: Array<Value | Error>) => Value | Error;
export type Cont = ContVal | ContArray;
export type ContVal = IfCont | FirstCont | SetCont | AppCont1 | ExpsCont1 | DefineCont | TopCont;
export type ContArray = LetCont | LetrecCont | AppCont2 | ExpsCont2;

export const isContVal = (x: any): x is ContVal => isIfCont(x) || isFirstCont(x) || isSetCont(x) ||
            isAppCont1(x) || isExpsCont1(x) || isDefineCont(x) || isTopCont(x);
export const isContArray = (x: any): x is ContArray => isLetCont(x) || isLetrecCont(x) || isAppCont2(x) || isExpsCont2(x);

 export interface TopCont {tag: "TopCont"};
export const makeTopCont = (): TopCont => ({tag: "TopCont"});
export const isTopCont = (x: any): x is TopCont => x.tag === "TopCont";

export interface IfCont {tag: "IfCont", exp: IfExp, env: Env, cont: Cont};
export const makeIfCont = (exp: IfExp, env: Env, cont: Cont): IfCont => ({tag: "IfCont", env: env, exp: exp, cont: cont});
export const isIfCont = (x: any): x is IfCont => x.tag === "IfCont";

export interface FirstCont {tag: "FirstCont", exps: Exp[], env: Env, cont: Cont};
export const makeFirstCont = (exps: Exp[], env: Env, cont: Cont): FirstCont => ({tag: "FirstCont", env: env, exps: exps, cont: cont});
export const isFirstCont = (x: any): x is FirstCont => x.tag === "FirstCont";

export interface SetCont {tag: "SetCont", exp: SetExp, env: Env, cont: Cont};
export const makeSetCont = (exp: SetExp, env: Env, cont: Cont): SetCont => ({tag: "SetCont", env: env, exp: exp, cont: cont});
export const isSetCont = (x: any): x is SetCont => x.tag === "SetCont";

export interface AppCont1 {tag: "AppCont1", exp: AppExp, env: Env, cont: Cont};
export const makeAppCont1 = (exp: AppExp, env: Env, cont: Cont): AppCont1 => ({tag: "AppCont1", env: env, exp: exp, cont: cont});
export const isAppCont1 = (x: any): x is AppCont1 => x.tag === "AppCont1";

export interface ExpsCont1 {tag: "ExpsCont1", exps: Exp[], env: Env, cont: Cont};
export const makeExpsCont1 = (exps: Exp[], env: Env, cont: Cont): ExpsCont1 => ({tag: "ExpsCont1", env: env, exps: exps, cont: cont});
export const isExpsCont1 = (x: any): x is ExpsCont1 => x.tag === "ExpsCont1";

export interface LetCont {tag: "LetCont", exp: LetExp, env: Env, cont: Cont};
export const makeLetCont = (exp: LetExp, env: Env, cont: Cont): LetCont => ({tag: "LetCont", env: env, exp: exp, cont: cont});
export const isLetCont = (x: any): x is LetCont => x.tag === "LetCont";

export interface LetrecCont {tag: "LetrecCont", exp: LetrecExp, env: ExtEnv, cont: Cont};
export const makeLetrecCont = (exp: LetrecExp, env: ExtEnv, cont: Cont): LetrecCont => ({tag: "LetrecCont", env: env, exp: exp, cont: cont});
export const isLetrecCont = (x: any): x is LetrecCont => x.tag === "LetrecCont";

export interface AppCont2 {tag: "AppCont2", proc: Value | Error, env: Env, cont: Cont};
export const makeAppCont2 = (proc: Value | Error, env: Env, cont: Cont): AppCont2 => ({tag: "AppCont2", proc: proc, env: env, cont: cont});
export const isAppCont2 = (x: any): x is AppCont2 => x.tag === "AppCont2";

export interface ExpsCont2 {tag: "ExpsCont2", firstVal: Value | Error, cont: Cont};
export const makeExpsCont2 = (firstVal: Value | Error, cont: Cont): ExpsCont2 => ({tag: "ExpsCont2", firstVal: firstVal, cont: cont});
export const isExpsCont2 = (x: any): x is ExpsCont2 => x.tag === "ExpsCont2";

export interface DefineCont {tag: "DefineCont", exps: Exp[], cont: Cont};
export const makeDefineCont = (exps: Exp[], cont: Cont): DefineCont => ({tag: "DefineCont", exps: exps, cont: cont});
export const isDefineCont = (x: any): x is DefineCont => x.tag === "DefineCont";

export type InstructionSet =
    'applyCont' | 'applyContVal' | 'applyContArray' | 'halt' |
    'applyIfCont' | 'applyFirstCont' | 'applySetCont' |
    'applyLetCont' | 'applyLetrecCont' | 'applyAppCont2' | 'applyExpsCont2' |
    'applyAppCont1' | 'applyExpsCont1' | 'applyDefineCont' |
    'applyTopCont' | 'evalCont' | 'evalIf' | 'evalProc' | 'evalApp' | 'evalSet' |
    'evalLet' | 'evalLetrec' | 'evalSequence' | 'evalExps' | 'evalDefineExps' |
    'applyProcedure' | 'applyClosure';

// ============================================================================
// REGISTERS
// Define global variable for registers - one for all the parameters of the functions
// involved in the interpreter.
export let contREG: Cont;
export let valREG: Value | Error;
export let valsREG: Array<Value | Error>;
export let expREG: Exp;
export let expsREG: Exp[];
export let envREG: Env;
export let pcREG: InstructionSet;

export let TRACE = false;
export let MAXCOUNT = 10000000;

export const dumpREG = () => {
    if (TRACE) {
        console.log(`In ${pcREG}: valREG = ${JSON.stringify(valREG)} - valsREG = ${JSON.stringify(valsREG)}`);
        console.log(`             expREG = ${JSON.stringify(expREG)} - expsREG = ${JSON.stringify(expsREG)}`);
        console.log(`             contREG = ${JSON.stringify(contREG)}`);
        console.log(`\n`);
    }
}

// ApplyCont dispatch on type of cont
// Type of val can be:
// - Value | Error for ContVal
// - Array<Value | Error> for ContArray
// ContVal = IfCont | FirstCont | SetCont | AppCont1 | ExpsCont1 | DefineCont | TopCont;
// ContArray = LetCont | LetrecCont | AppCont2 | ExpsCont2;
const isValue = (x: any): x is Value => (x === undefined) || isSExp(x) || isError(x);
const isValueArray = (x: any): x is Array<Value | Error> => isArray(x);

// const applyCont = (cont: Cont, val: Value | Error | Array<Value | Error>): Value | Error =>
// @@ Expect val in valREG or valsREG depending on type
export const applyCont = (): void => {
    if (isContVal(contREG))
        pcREG = 'applyContVal';
    else
        pcREG = 'applyContArray';
}

// type ContVal = IfCont | FirstCont | SetCont | AppCont1 | ExpsCont1 | DefineCont | TopCont;
// const applyContVal = (cont: ContVal, val: Value | Error): Value | Error =>
export const applyContVal = (): void => {
    // dumpREG();
    pcREG =
    isIfCont(contREG) ? 'applyIfCont' :
    isFirstCont(contREG) ? 'applyFirstCont' :
    isSetCont(contREG) ? 'applySetCont' :
    isAppCont1(contREG) ? 'applyAppCont1' :
    isExpsCont1(contREG) ? 'applyExpsCont1' :
    isDefineCont(contREG) ? 'applyDefineCont' :
    isTopCont(contREG) ? 'applyTopCont' :
    (console.error(`Unknown cont ${contREG}`), 'halt');
}

// type ContArray = LetCont | LetrecCont | AppCont2 | ExpsCont2;
// const applyContArray = (cont: ContArray, vals: Array<Value | Error>): Value | Error =>
export const applyContArray = (): void => {
    // dumpREG();
    pcREG =
    isLetCont(contREG) ? 'applyLetCont' :
    isLetrecCont(contREG) ? 'applyLetrecCont' :
    isAppCont2(contREG) ? 'applyAppCont2' :
    isExpsCont2(contREG) ? 'applyExpsCont2' :
    (console.error(`Unknown cont ${contREG}`), 'halt');
}

// const applyTopCont = (cont: TopCont, val: Value | Error): Value | Error => {
export const applyTopCont = (): void => {
    console.log(SExpToString(valREG));
    pcREG = 'halt';
}

// const applyIfCont = (cont: IfCont, val: Value | Error): Value | Error =>
export const applyIfCont = (): void => {
    dumpREG();
    if (isIfCont(contREG)) {
        if (isError(valREG)) {
            contREG = contREG.cont;
            pcREG = 'applyCont';
        } else if (isTrueValue(valREG)) {
            expREG = contREG.exp.then;
            envREG = contREG.env;
            contREG = contREG.cont;
            pcREG = 'evalCont';
        } else {
            expREG = contREG.exp.alt;
            envREG = contREG.env;
            contREG = contREG.cont;
            pcREG = 'evalCont';
        }
    } else {
        console.error(`Unknown cont ${contREG}`);
        pcREG = 'halt';
    }
}

// const applyLetCont = (cont: LetCont, vals: Array<Value | Error>): Value | Error =>
export const applyLetCont = (): void => {
    dumpREG();
    if (isLetCont(contREG)) {
        if (hasNoError(valsREG)) {
            expsREG = contREG.exp.body;
            envREG = makeExtEnv(letVars(contREG.exp), valsREG, contREG.env);
            contREG = contREG.cont;
            pcREG = 'evalSequence';
        } else {
            valREG = Error(getErrorMessages(valsREG));
            contREG = contREG.cont;
            pcREG = 'applyCont';
        }
    } else {
        console.error(`Unknown cont ${contREG}`);
        pcREG = 'halt';
    }
}

// export const applyFirstCont = (cont: FirstCont, val: Value | Error): Value | Error =>
export const applyFirstCont = (): void => {
    dumpREG();
    if (isFirstCont(contREG)) {
        if (isError(valREG)) {
            contREG = contREG.cont;
            pcREG = 'applyCont';
        } else {
            expsREG = rest(contREG.exps);
            envREG = contREG.env;
            contREG = contREG.cont;
            pcREG = 'evalSequence';
        }
    } else {
        console.error(`Unknown cont ${contREG}`);
        pcREG = 'halt';
    }
}

// export const applyLetrecCont = (cont: LetrecCont, vals: Array<Value | Error>): Value | Error => {
export const applyLetrecCont = (): void => {
    dumpREG();
    if (isLetrecCont(contREG)) {
        if (hasNoError(valsREG)) {
            // Bind vars in extEnv to the new values
            zipWith((bdg, cval) => setFBinding(bdg, cval), contREG.env.frame.fbindings, valsREG);
            expsREG = contREG.exp.body;
            envREG = contREG.env;
            contREG = contREG.cont;
            pcREG = 'evalSequence';
        } else {
            valREG = Error(getErrorMessages(valsREG));
            contREG = contREG.cont;
            pcREG = 'applyCont';
        }
    } else {
        console.error(`Unknown cont ${contREG}`);
        pcREG = 'halt';
    }
}

// export const applySetCont = (cont: SetCont, val: Value | Error): Value | Error => {
export const applySetCont = (): void => {
    dumpREG();
    if (isSetCont(contREG)) {
        if (isError(valREG)) {
            contREG = contREG.cont;
            pcREG = 'applyCont';
        } else {
            const v = contREG.exp.var.var;
            const bdg = applyEnvBdg(contREG.env, v);
            if (isError(bdg)) {
                valREG = Error(`Var not found ${v}`);
                contREG = contREG.cont;
                pcREG = 'applyCont';
            } else {
                setFBinding(bdg, valREG);
                valREG = undefined;
                contREG = contREG.cont;
                pcREG = 'applyCont';
            }
        }
    } else {
        console.error(`Unknown cont ${contREG}`);
        pcREG = 'halt';
    }
}

// export const applyAppCont1 = (cont: AppCont1, val: Value | Error): Value | Error =>
export const applyAppCont1 = (): void => {
    dumpREG();
    if (isAppCont1(contREG)) {
        expsREG = contREG.exp.rands;
        envREG = contREG.env;
        contREG = makeAppCont2(valREG, contREG.env, contREG.cont)
        pcREG = 'evalExps';
    } else {
        console.error(`Unknown cont ${contREG}`);
        pcREG = 'halt';
    }
}

// export const applyAppCont2 = (cont: AppCont2, vals: Array<Value | Error>): Value | Error =>
export const applyAppCont2 = (): void => {
    dumpREG();
    if (isAppCont2(contREG)) {
        valREG = contREG.proc;
        contREG = contREG.cont;
        pcREG = 'applyProcedure';
    } else {
        console.error(`Unknown cont ${contREG}`);
        pcREG = 'halt';
    }
}

// export const applyExpsCont1 = (cont: ExpsCont1, val: Value | Error): Value | Error =>
export const applyExpsCont1 = (): void => {
    dumpREG();
    if (isExpsCont1(contREG)) {
        expsREG = rest(contREG.exps);
        envREG = contREG.env;
        contREG = makeExpsCont2(valREG, contREG.cont);
        pcREG = 'evalExps';
    } else {
        console.error(`Unknown cont ${contREG}`);
        pcREG = 'halt';
    }
}

// export const applyExpsCont2 = (cont: ExpsCont2, vals: Array<Value | Error>): Value | Error =>
export const applyExpsCont2 = (): void => {
    dumpREG();
    if (isExpsCont2(contREG)) {
        valsREG = [contREG.firstVal, ...valsREG];
        contREG = contREG.cont;
        pcREG = 'applyCont';
    } else {
        console.error(`Unknown cont ${contREG}`);
        pcREG = 'halt';
    }
}

// export const applyDefineCont = (cont: DefineCont, val: Value | Error): Value | Error => {
export const applyDefineCont = (): void => {
    dumpREG();
    if (isDefineCont(contREG)) {
        if (isError(valREG)) {
            contREG = contREG.cont;
            pcREG = 'applyCont';
        } else {
            globalEnvAddBinding(first(contREG.exps).var.var, valREG);
            expsREG = rest(contREG.exps);
            envREG = theGlobalEnv;
            contREG = contREG.cont;
            pcREG = 'evalSequence';
        }
    } else {
        console.error(`Unknown cont ${contREG}`);
        pcREG = 'halt';
    }
}

// ========================================================
// Eval functions

// export const evalCont = (exp: CExp | Error, env: Env, cont: Cont): Value | Error =>
export const evalCont = (): void => {
    dumpREG();
    if (isError(expREG)) {
        valREG = expREG;
        pcREG = 'applyCont';
    } else if (isNumExp(expREG)) {
        valREG = expREG.val;
        pcREG = 'applyCont';
    } else if (isBoolExp(expREG)) {
        valREG = expREG.val;
        pcREG = 'applyCont';
    } else if (isStrExp(expREG)) {
        valREG = expREG.val;
        pcREG = 'applyCont';
    } else if (isPrimOp(expREG)) {
        valREG = expREG;
        pcREG = 'applyCont';
    } else if (isVarRef(expREG)) {
        valREG = applyEnv(envREG, expREG.var);
        pcREG = 'applyCont';
    } else if (isLitExp(expREG)) {
        valREG = expREG.val;
        pcREG = 'applyCont';
    } else if (isIfExp(expREG)) {
        pcREG = 'evalIf';
    } else if (isProcExp(expREG)) {
        pcREG = 'evalProc';
    } else if (isLetExp(expREG)) {
        pcREG = 'evalLet';
    } else if (isLetrecExp(expREG)) {
        pcREG = 'evalLetrec';
    } else if (isSetExp(expREG)) {
        pcREG = 'evalSet';
    } else if (isAppExp(expREG)) {
        pcREG = 'evalApp';
    } else {
        valREG = Error(`Bad L5 AST ${expREG}`);
        pcREG = 'applyCont';
    }
}

export const isTrueValue = (x: Value | Error): boolean | Error =>
    isError(x) ? x :
    ! (x === false);

// const evalIf = (exp: IfExp, env: Env, cont: Cont): Value | Error =>
export const evalIf = (): void => {
    dumpREG();
    if (isIfExp(expREG)) {
        contREG = makeIfCont(expREG, envREG, contREG);
        expREG = expREG.test;
        pcREG = 'evalCont';
    } else {
        valREG = Error(`Bad expREG in evalIf ${expREG}`);
        pcREG = 'halt';
    }
}

// const evalProc = (exp: ProcExp, env: Env, cont: Cont): Value | Error =>
export const evalProc = (): void => {
    dumpREG();
    if (isProcExp(expREG)) {
        valREG = makeClosure(expREG.args, expREG.body, envREG);
        pcREG = 'applyCont';
    } else {
        valREG = Error(`Bad expREG in evalProc ${expREG}`);
        pcREG = 'halt';
    }
}

// Return the vals (rhs) of the bindings of a let expression
const letVals = (exp: LetExp | LetrecExp): CExp[] =>
        map((b) => b.val, exp.bindings);

// Return the vars (lhs) of the bindings of a let expression
const letVars = (exp: LetExp | LetrecExp): string[] =>
        map((b) => b.var.var, exp.bindings);

// LET: Direct evaluation rule without syntax expansion
// compute the values, extend the env, eval the body.
// const evalLet = (exp: LetExp, env: Env, cont: Cont): Value | Error =>
export const evalLet = (): void => {
    dumpREG();
    if (isLetExp(expREG)) {
        expsREG = letVals(expREG);
        contREG = makeLetCont(expREG, envREG, contREG);
        pcREG = 'evalExps';
    } else {
        valREG = Error(`Bad expREG in evalLet ${expREG}`);
        pcREG = 'halt';
    }
}

// Evaluate an array of expressions in sequence - pass the result of the last element to cont
// @Pre: exps is not empty
// export const evalSequence = (exps: Exp[], env: Env, cont: Cont): Value | Error =>
export const evalSequence = (): void => {
    dumpREG();
    if (isEmpty(expsREG)) {
        valREG = Error("Empty Sequence");
        pcREG = 'applyCont';
    } else if (isDefineExp(first(expsREG))) {
        pcREG = 'evalDefineExps';
    } else if (isEmpty(rest(expsREG))) {
        expREG = first(expsREG);
        pcREG = 'evalCont';
    } else {
        expREG = first(expsREG);
        contREG = makeFirstCont(expsREG, envREG, contREG);
        pcREG = 'evalCont';
    }
}

// LETREC: Direct evaluation rule without syntax expansion
// 1. extend the env with vars initialized to void (temporary value)
// 2. compute the vals in the new extended env
// 3. update the bindings of the vars to the computed vals
// 4. compute body in extended env
// export const evalLetrec = (exp: LetrecExp, env: Env, cont: Cont): Value | Error => {
export const evalLetrec = (): void => {
    dumpREG();
    if (isLetrecExp(expREG)) {
        const vars = letVars(expREG);
        const vals = letVals(expREG);
        const extEnv = makeExtEnv(vars, repeat(undefined, vars.length), envREG);
        // Compute the vals in the extended env
        expsREG = vals;
        envREG = extEnv;
        contREG = makeLetrecCont(expREG, extEnv, contREG);
        pcREG = 'evalExps';
    } else {
        valREG = Error(`Bad expREG in evalLetrec ${expREG}`);
        pcREG = 'halt';
    }
}

// Handling of mutation with set!
// export const evalSet = (exp: SetExp, env: Env, cont: Cont): Value | Error =>
export const evalSet = (): void => {
    dumpREG();
    if (isSetExp(expREG)) {
        contREG = makeSetCont(expREG, envREG, contREG);
        expREG = expREG.val;
        pcREG = 'evalCont';
    } else {
        valREG = Error(`Bad expREG in evalSet ${expREG}`);
        pcREG = 'halt';
    }
}

// export const evalApp = (exp: AppExp, env: Env, cont: Cont): Value | Error =>
export const evalApp = (): void => {
    dumpREG();
    if (isAppExp(expREG)) {
        contREG = makeAppCont1(expREG, envREG, contREG);
        expREG = expREG.rator;
        pcREG = 'evalCont';
    } else {
        valREG = Error(`Bad expREG in evalApp ${expREG}`);
        pcREG = 'halt';
    }
}

// KEY: This procedure does NOT have an env parameter.
//      Instead we use the env of the closure.
// export const applyProcedure = (proc: Value | Error, args: Array<Value | Error>, cont: Cont): Value | Error =>
// Arguments in valREG, valsREG, contREG
export const applyProcedure = (): void => {
    dumpREG();
    if (isError(valREG)) {
        pcREG = 'applyCont';
    } else if (!hasNoError(valsREG)) {
        valREG = Error(`Bad argument: ${getErrorMessages(valsREG)}`);
        pcREG = 'applyCont';
    } else if (isPrimOp(valREG)) {
        valREG = applyPrimitive(valREG, valsREG);
        pcREG = 'applyCont';
    } else if (isClosure(valREG)) {
        pcREG = 'applyClosure';
    } else {
        valREG = Error(`Bad procedure ${JSON.stringify(valREG)}`);
        pcREG = 'applyCont';
    }
}

// export const applyClosure = (proc: Closure, args: Value[], cont: Cont): Value | Error => {
// Parameters in proc = valREG, args = valsREG
export const applyClosure = (): void => {
    dumpREG();
    if (isClosure(valREG)) {
        let vars = map((v: VarDecl) => v.var, valREG.params);
        expsREG = valREG.body;
        // This noError was tested in applyProcedure
        // but we don't keep the type across procedures
        if (hasNoError(valsREG)) {
            envREG = makeExtEnv(vars, valsREG, valREG.env);
            pcREG = 'evalSequence';
        } else {
            valREG = Error(`Bad argument: ${getErrorMessages(valsREG)}`);
            pcREG = 'applyCont';
        }
    } else {
        valREG = Error(`Bad expREG in evalApp ${expREG}`);
        pcREG = 'halt';
    }
}

// Evaluate an array of expressions - pass the result as an array to the continuation
// export const evalExps = (exps: Exp[], env: Env, cont: ContArray): Value | Error =>
export const evalExps = (): void => {
    dumpREG();
    if (isEmpty(expsREG)) {
        valsREG = [];
        pcREG = 'applyCont';
    } else {
        expREG = first(expsREG);
        contREG = makeExpsCont1(expsREG, envREG, contREG);
        pcREG = 'evalCont';
    }
}

// define always updates theGlobalEnv
// We only expect defineExps at the top level.
// const evalDefineExps = (exps: Exp[], cont: Cont): Value | Error =>
export const evalDefineExps = (): void => {
    dumpREG();
    if (isDefineExp(first(expsREG))) {
        expREG = first(expsREG).val;
        envREG = theGlobalEnv;
        contREG = makeDefineCont(expsREG, contREG);
        pcREG = 'evalCont';
    } else {
        valREG = Error(`Bad expsREG in evalDefine ${first(expsREG)}`);
        pcREG = 'halt';
    }
}

// Evaluate a program
// Main program - EVALUATION LOOP of the Virtual Machine
export const evalProgram = (program: Program): Value | Error => {
    valREG = undefined;
    valsREG = undefined;
    expsREG = program.exps;
    envREG = theGlobalEnv;
    contREG = makeTopCont();
    pcREG = 'evalSequence';
    /* Instruction set
    'applyCont' | 'applyContVal' | 'applyContArray' | 'halt' |
    'applyIfCont' | 'applyFirstCont' | 'applySetCont' |
    'applyLetCont' | 'applyLetrecCont' | 'applyAppCont2' | 'applyExpsCont2' |
    'applyAppCont1' | 'applyExpsCont1' | 'applyDefineCont' |
    'applyTopCont' | 'evalCont' | 'evalIf' | 'evalProc' | 'evalApp' | 'evalSet' |
    'evalLet' | 'evalLetrec' | 'evalSequence' | 'evalExps' | 'evalDefineExps' |
    'applyProcedure' | 'applyClosure';
    */
    let count = 0;
    while (true) {
        count++;
        if (pcREG === 'evalSequence') evalSequence();
        else if (pcREG === 'halt') break;
        else if (pcREG === 'applyCont') applyCont();
        else if (pcREG === 'applyContVal') applyContVal();
        else if (pcREG === 'applyContArray') applyContArray();
        else if (pcREG === 'applyIfCont') applyIfCont();
        else if (pcREG === 'applyFirstCont') applyFirstCont();
        else if (pcREG === 'applySetCont') applySetCont();
        else if (pcREG === 'applyLetCont') applyLetCont();
        else if (pcREG === 'applyLetrecCont') applyLetrecCont();
        else if (pcREG === 'applyAppCont2') applyAppCont2();
        else if (pcREG === 'applyExpsCont2') applyExpsCont2();
        else if (pcREG === 'applyAppCont1') applyAppCont1();
        else if (pcREG === 'applyExpsCont1') applyExpsCont1();
        else if (pcREG === 'applyDefineCont') applyDefineCont();
        else if (pcREG === 'applyTopCont') applyTopCont();
        else if (pcREG === 'evalCont') evalCont();
        else if (pcREG === 'evalIf') evalIf();
        else if (pcREG === 'evalApp') evalApp();
        else if (pcREG === 'evalProc') evalProc();
        else if (pcREG === 'evalSet') evalSet();
        else if (pcREG === 'evalLet') evalLet();
        else if (pcREG === 'evalLetrec') evalLetrec();
        else if (pcREG === 'evalExps') evalExps();
        else if (pcREG === 'evalDefineExps') evalDefineExps();
        else if (pcREG === 'applyProcedure') applyProcedure();
        else if (pcREG === 'applyClosure') applyClosure();
        else {
            console.error(`Bad instruction: ${pcREG}`);
            break;
        }
        if (count > MAXCOUNT) {
            console.error(`STOP: ${count} instructions`);
            dumpREG();
            break;
        }
    }
    return valREG;
}

export const evalParse = (s: string): Value | Error => {
    let ast: Parsed | Error = parse(s);
    if (isProgram(ast)) {
        return evalProgram(ast);
    } else if (isExp(ast)) {
        return evalProgram(makeProgram([ast]));
    } else {
        return ast;
    }
}

// For read-eval-print-loop - print a readable value
export const SExpToString = (s: Value | Error): string =>
    isNumber(s) ? `${s}` :
    isBoolean(s) ? `${s}` :
    isString(s) ? s :
    isPrimOp(s) ? `${s.op}` :
    isClosure(s) ? `<Closure (${map((s) => s.var, s.params)}) ${map(unparse, s.body).join(" ")}>` :
    isSymbolSExp(s) ? `${s.val}` :
    isEmptySExp(s) ? `()` :
    isCompoundSExp(s) ? `(${map((s) => SExpToString(s), s.val).join(" ")})` :
    isError(s) ? `Error: ${s.message}` :
    `Unknown value ${s}`;


// ========================================================
// Primitives (Unchanged in L6)

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


