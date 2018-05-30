import assert = require("assert");
import deepEqual = require("deep-equal");
import { map, zipWith } from 'ramda';
import * as S from "./L5-substitution-adt";
import { makeTVar, parseTE, unparseTExp, TExp } from "./TExp";
import { hasNoError, isError } from './error';

// Setup

// The empty substitution
export const sub0 = S.makeEmptySub();

// Safe parser
export const p = (t: string): TExp => {
    const te = parseTE(t);
    return isError(te) ? makeTVar("Error") : te;
};
// Sub constructor from concrete syntax
export const sub = (vars: string[], tes: string[]): S.Sub => {
    const res = S.makeSub(map(makeTVar, vars), map(p, tes));
    return (isError(res)) ? S.makeEmptySub() : res;
}

// Facilitate comparisons in a readable manner
export interface VarTe {v: string; te: string};
export const makeVarTe = (v: string, te: string): VarTe => ({v: v, te: te});
export const subToVarsTes = (sub: S.Sub): VarTe[] =>
    zipWith(makeVarTe, map(unparseTExp, sub.vars),
                       map(unparseTExp, sub.tes)).sort();
export const subToStr = (sub: S.Sub): string =>
    `{${zipWith((v, t) => `${v.var}:${unparseTExp(t)}`, sub.vars, sub.tes).sort().join(", ")}}`;

// Compare 2 subs encoded as VarTe (set equality)
export const eqSub = (sub1: S.Sub, sub2: S.Sub): boolean =>
    hasNoError([sub1, sub2]) && deepEqual(subToStr(sub1), subToStr(sub2));

const assertEqSub = (sub: S.Sub | Error, expected: S.Sub): void => {
    if (! isError(sub)) {
        if (! eqSub(sub, expected))
            console.error(`${subToStr(sub)} instead of\n${subToStr(expected)}`);
    } else
        console.error(sub);
};

// {T1:number, T2:(T4 -> number), T3:T9}
export const sub1 = sub(["T1", "T2", "T3"],
                 ["number", "(T4 -> number)", "T9"]);

// {T4:(T1->number), T5:boolean, T6:T7}
export const sub2 = sub(["T4", "T5", "T6"],
                 ["(T1 -> number)", "boolean", "T7"]);

// {T7:number, T8:[T5 * number -> T3], T9:boolean}
export const sub3 = sub(["T7", "T8", "T9"],
                 ["number", "(T5 * number -> T3)", "boolean"]);

// {T1:boolean, T2:(number -> T10), (T5 * boolean -> number)}
export const sub4 = sub(["T1", "T2", "T3"],
                 ["boolean", "(number -> T10)", "(T5 * boolean -> number)"]);

// {T1:boolean, T2:(T5*boolean), T3:number}
export const sub5 = sub(["T1", "T2", "T3"],
                 ["boolean", "(T5 * boolean -> number)", "number"]);

// Tests
// console.log(subToStr(sub1));
// console.log(subToStr(sub2));
// console.log(subToStr(sub3));
// console.log(subToStr(sub4));
// console.log(subToStr(sub5));

// makeSub with circular dependency
{
    const te1 = parseTE("(number -> T1)");
    if (! isError(te1)) {
        const sub1 = S.makeSub([makeTVar("T1")], [te1]);
        assert(isError(sub1));
        // console.log(sub1);
    }
}

// applySub
{
    const sub1 = sub(["T1", "T2"], ["number", "boolean"]);
    const te1 = parseTE("(T1 * T2 -> T1)");
    if (! isError(te1)) {
        const te2 = S.applySub(sub1, te1);
        assert(unparseTExp(te2) === "(number * boolean -> number)");
    }
}

// combineSub

// {T1:(number -> S1), T2:(number -> S4)} o {T3:(number -> S2)} =>
// {T1:(number -> S1), T2:(number -> S4), T3:(number -> S2)}
{
    const sub1 = sub(["T1", "T2"],
                     ["(number -> S1)", "(number -> S4)"]);
    const sub2 = sub(["T3"], ["(number -> S2)"]);
    const expected = sub(["T1", "T2", "T3"],
                         ["(number -> S1)", "(number -> S4)", "(number -> S2)"]);
    const res = S.combineSub(sub1, sub2);
    assertEqSub(res, expected);
}

// {T1:(number -> S1), T2:(number -> T5)} o {T3:(number -> S2), T4:(number -> S1), T5:boolean} =>
// {T1:(number -> S1), T2:(number -> boolean), T3:(number -> S2), T4:(number -> S1), T5:boolean}
{
    const sub1 = sub(["T1", "T2"],
                     ["(number -> S1)", "(number -> T5)"]);
    const sub2 = sub(["T3", "T4", "T5"],
                     ["(number -> S2)", "(number -> S1)", "boolean"]);
    const expected = sub(["T1", "T2", "T3", "T4", "T5"],
                         ["(number -> S1)", "(number -> boolean)", "(number -> S2)", "(number -> S1)", "boolean"]);
    const res = S.combineSub(sub1, sub2);
    assertEqSub(res, expected);
}

// {T1:(number -> S1), T2:(T5 -> T4)} o {S1:boolean, T3:(number -> S2), T5:(number -> S1), T4:boolean} =>
// {T1:{number -> boolean}, T2:((number -> S1) -> boolean), T3:(number -> S2), T4:boolean, T5:(number -> S1), S1:boolean}
{
    const sub1 = sub(["T1", "T2"],
                     ["(number -> S1)", "(T5 -> T4)"]);
    const sub2 = sub(["S1", "T3", "T4", "T5"],
                     ["boolean", "(number -> S2)", "boolean", "(number -> S1)"]);
    const expected = sub(["T1", "T2", "T3", "T4", "T5", "S1"],
                         ["(number -> boolean)", "((number -> S1) -> boolean)", "(number -> S2)", "boolean", "(number -> S1)", "boolean"]);
    const res = S.combineSub(sub1, sub2);
    assertEqSub(res, expected);
}

// {T1:S1, T2:(S2 -> number), T3:boolean} o {S1:(T5 -> (number * T2 -> T2)), S2:T3} =>
// {T1:(T5 -> (number * T2 -> T2)), T2:(T3 -> number), T3:boolean, S1:(T5 -> (number * T2 -> T2)), S2:T3}
{
    const sub1 = sub(["T1", "T2", "T3"],
                     ["S1", "(S2 -> number)", "boolean"]);
    const sub2 = sub(["S1", "S2"],
                     ["(T5 -> (number * T2 -> T2))", "T3"]);
    const expected = sub(["T1", "T2", "T3", "S1", "S2"],
                         ["(T5 -> (number * T2 -> T2))", "(T3 -> number)", "boolean", "(T5 -> (number * T2 -> T2))", "T3"]);
    const res = S.combineSub(sub1, sub2);
    assertEqSub(res, expected);
}

// {T1:S1, T2:(S2 -> number), T3:boolean} o {S1:(T5 -> (number * T2 -> T2)), S2:T3} =>
// {T1:(T5 -> (number * T2 -> T2)), T2:(T3 -> number), T3:boolean, S1:(T5 -> (number * T2 -> T2)), S2:T3}
{
    const sub1 = sub(["T1", "T2", "T3"],
                     ["S1", "(S2 -> number)", "boolean"]);
    const sub2 = sub(["S1", "S2"],
                     ["(T5 -> (number * T2 -> T2))", "T3"]);
    const expected = sub(["T1", "T2", "T3", "S1", "S2"],
                         ["(T5 -> (number * T2 -> T2))", "(T3 -> number)", "boolean",
                          "(T5 -> (number * T2 -> T2))", "T3"]);
    const res = S.combineSub(sub1, sub2);
    assertEqSub(res, expected);
}

// {T1:number, T2:(T4 -> number), T3:T9} o {T4:(T1 -> number), T5:boolean, T6:T7} =>
// {T1:number, T2:((T1 -> number) -> number), T3:T9, T4:(T1 -> number), T5:boolean, T6:T7}
{
    const sub1 = sub(["T1", "T2", "T3"],
                     ["number", "(T4 -> number)", "T9"]);
    const sub2 = sub(["T4", "T5", "T6"],
                     ["(T1 -> number)", "boolean", "T7"]);
    const expected = sub(["T1", "T2", "T3", "T4", "T5", "T6"],
                         ["number", "((T1 -> number) -> number)", "T9", "(T1 -> number)", "boolean", "T7"]);
    const res = S.combineSub(sub1, sub2);
    assertEqSub(res, expected);
}

// Circular substitution
// {T3:boolean, S1:(number -> T2), T4:(number -> S1), T5:boolean} o {T1:(number -> S1), T2:(T3 -> S1)}
// Error
{
    const sub1 = sub(["T3", "T4", "T5", "S1"],
                     ["boolean", "(number -> S1)", "boolean", "(number -> T2)"]);
    const sub2 = sub(["T1", "T2"],
                     ["(number -> S1)", "(T3 -> S1)"]);
    const res = S.combineSub(sub1, sub2);
    // console.log(res);
    assert(isError(res));
}

// Combine with overlapping var
// {T3:boolean, S1:(number -> T2), T4:(number -> S1), T5:boolean} o {T1:(number -> S1), T2:(T3 -> S1)}
// Error
{
    const sub1 = sub(["T7", "T8"],
                     ["number", "(T5 * number -> T3)"]);
    const sub2 = sub(["T5", "T8"],
                     ["T7", "boolean"]);
    const expected = sub(["T5", "T7", "T8"],
                         ["T7", "number", "(T7 * number -> T3)"]);
    const res = S.combineSub(sub1, sub2);
    assertEqSub(res, expected);
}

// Extend-sub

// Combine with overlapping var
// {T3:boolean, S1:(number -> T2), T4:(number -> S1), T5:boolean} o {T1:(number -> S1), T2:(T3 -> S1)}
// Error
{
    const sub1 = sub(["T1", "T2", "T3"],
                     ["S1", "(S1 -> number)", "boolean"]);
    const v2 = makeTVar("S1");
    const t2 = p("(T21 -> (number * T23 -> T22))");
    const expected = sub(["T1", "T2", "T3", "S1"],
                         ["(T21 -> (number * T23 -> T22))", "((T21 -> (number * T23 -> T22)) -> number)",
                          "boolean", "(T21 -> (number * T23 -> T22))"]);
    const res = S.extendSub(sub1, v2, t2);
    assertEqSub(res, expected);
}
