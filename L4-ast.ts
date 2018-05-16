// ===========================================================
// AST type models for L4
// L4 extends L3 with:
// letrec and set!

import * as assert from "assert";
import { all, apply, filter, map, reduce, zipWith } from "ramda";
import { AtomicExp, VarDecl, VarRef } from './L3-ast';
import { isAtomicExp } from './L3-ast';
import { isArray, isEmpty, isNumericString, isSexpString, isString } from './L3-ast';
import { makeVarDecl, makeVarRef } from './L3-ast';
import { parseDecls, parseL3Atomic } from './L3-ast';
import { makeEmptySExp, makeSymbolSExp } from './L3-value';
import { makeCompoundSExp4, SExp4 } from './L4-value';
import { getErrorMessages, hasNoError, isError, safeF, safeFL } from './error';
import { allT, first, rest, second } from './list';

/*
;; =============================================================================
;; Scheme Parser
;;
;; L2 extends L1 with support for IfExp and ProcExp
;; L3 extends L2 with support for:
;; - Pair and List datatypes
;; - Compound literal expressions denoted with quote
;; - Primitives: cons, car, cdr, list?
;; - The empty-list literal expression
;; - The Let abbreviation is also supported.
;; L4 extends L3 with:
;; - letrec
;; - set!

;; <program4> ::= (L4 <exp4>+) // Program4(exps:List(exp4))
;; <exp4> ::= <define> | <cexp4>              / DefExp | CExp4
;; <define> ::= ( define <var> <cexp> )       / DefExp(var:VarDecl, val:CExp)
;; <var> ::= <identifier>                     / VarRef(var:string)
;; <cexp> ::= <number>                        / NumExp(val:number)
;;         |  <boolean>                       / BoolExp(val:boolean)
;;         |  <string>                        / StrExp(val:string)
;;         |  ( lambda ( <var>* ) <cexp>+ )   / ProcExp(params:VarDecl[], body:CExp[]))
;;         |  ( if <cexp> <cexp> <cexp> )     / IfExp(test: CExp, then: CExp, alt: CExp)
;;         |  ( let ( <binding>* ) <cexp>+ )  / LetExp(bindings:Binding[], body:CExp[]))
;;         |  ( quote <sexp> )                / LitExp(val:SExp)
;;         |  ( <cexp> <cexp>* )              / AppExp(operator:CExp, operands:CExp[]))
;;         |  ( letrec ( binding*) <cexp>+ )  / LetrecExp(bindings:Bindings[], body: CExp) #### L4
;;         |  ( set! <var> <cexp>)            / SetExp(var: varRef, val: CExp)             #### L4
;; <binding>  ::= ( <var> <cexp> )            / Binding(var:VarDecl, val:Cexp)
;; <prim-op>  ::= + | - | * | / | < | > | = | not |  eq? | string=?
;;                  | cons | car | cdr | list? | number?
;;                  | boolean? | symbol? | string?      ##### L3
;; <num-exp>  ::= a number token
;; <bool-exp> ::= #t | #f
;; <var-ref>  ::= an identifier token
;; <var-decl> ::= an identifier token
;; <sexp>     ::= symbol | number | bool | string | ( <sexp>* )              ##### L3
*/

// A value returned by parseL4
export type Parsed4 = Exp4 | Program4;

export type Exp4 = DefineExp4 | CExp4;
export type CompoundExp4 = AppExp4 | IfExp4 | ProcExp4 | LetExp4 | LitExp4 | LetrecExp4 | SetExp4;
export type CExp4 =  AtomicExp | CompoundExp4;

export interface Program4 {tag: "Program4"; exps: Exp4[]; };
export interface DefineExp4 {tag: "DefineExp4"; var: VarDecl; val: CExp4; };
export interface AppExp4 {tag: "AppExp4"; rator: CExp4; rands: CExp4[]; };
// L2
export interface IfExp4 {tag: "IfExp4"; test: CExp4; then: CExp4; alt: CExp4; };
export interface ProcExp4 {tag: "ProcExp4"; args: VarDecl[], body: CExp4[]; };
export interface Binding4 {tag: "Binding4"; var: VarDecl; val: CExp4; };
// L3
export interface LetExp4 {tag: "LetExp4"; bindings: Binding4[]; body: CExp4[]; };
export interface LitExp4 {tag: "LitExp4"; val: SExp4; };
// L4
export interface LetrecExp4 {tag: "LetrecExp4"; bindings: Binding4[]; body: CExp4[]; };
export interface SetExp4 {tag: "SetExp4"; var: VarRef; val: CExp4; };

// Type value constructors for disjoint types
export const makeProgram4 = (exps: Exp4[]): Program4 => ({tag: "Program4", exps: exps});
export const makeDefineExp4 = (v: VarDecl, val: CExp4): DefineExp4 =>
    ({tag: "DefineExp4", var: v, val: val});
export const makeAppExp4 = (rator: CExp4, rands: CExp4[]): AppExp4 =>
    ({tag: "AppExp4", rator: rator, rands: rands});
// L2
export const makeIfExp4 = (test: CExp4, then: CExp4, alt: CExp4): IfExp4 =>
    ({tag: "IfExp4", test: test, then: then, alt: alt});
export const makeProcExp4 = (args: VarDecl[], body: CExp4[]): ProcExp4 =>
    ({tag: "ProcExp4", args: args, body: body});
export const makeBinding4 = (v: VarDecl, val: CExp4): Binding4 =>
    ({tag: "Binding4", var: v, val: val});
// L3
export const makeLetExp4 = (bindings: Binding4[], body: CExp4[]): LetExp4 =>
    ({tag: "LetExp4", bindings: bindings, body: body});
export const makeLitExp4 = (val: SExp4): LitExp4 =>
    ({tag: "LitExp4", val: val});
// L4
export const makeLetrecExp4 = (bindings: Binding4[], body: CExp4[]): LetrecExp4 =>
    ({tag: "LetrecExp4", bindings: bindings, body: body});
export const makeSetExp4 = (v: VarRef, val: CExp4): SetExp4 =>
    ({tag: "SetExp4", var: v, val: val});

// Type predicates for disjoint types
export const isProgram4 = (x: any): x is Program4 => x.tag === "Program4";
export const isDefineExp4 = (x: any): x is DefineExp4 => x.tag === "DefineExp4";
export const isAppExp4 = (x: any): x is AppExp4 => x.tag === "AppExp4";
// L2
export const isIfExp4 = (x: any): x is IfExp4 => x.tag === "IfExp4";
export const isProcExp4 = (x: any): x is ProcExp4 => x.tag === "ProcExp4";
export const isBinding4 = (x: any): x is Binding4 => x.tag === "Binding4";
export const isLetExp4 = (x: any): x is LetExp4 => x.tag === "LetExp4";
export const isLitExp4 = (x: any): x is LitExp4 => x.tag === "LitExp4";
export const isLetrecExp4 = (x: any): x is LetrecExp4 => x.tag === "LetrecExp4";
export const isSetExp4 = (x: any): x is SetExp4 => x.tag === "SetExp4";

// Type predicates for type unions
export const isExp4 = (x: any): x is Exp4 => isDefineExp4(x) || isCExp4(x);
export const isCompoundExp4 = (x: any): x is CompoundExp4 =>
    isAppExp4(x) || isIfExp4(x) || isProcExp4(x) || isLitExp4(x) || isLetExp4(x) || isLetrecExp4(x) || isSetExp4(x);
export const isCExp4 = (x: any): x is CExp4 =>
    isAtomicExp(x) || isCompoundExp4(x);

// ========================================================
// Parsing

import p = require("s-expression");

export const parseL4 = (x: string): Parsed4 | Error =>
    parseL4Sexp(p(x));

export const parseL4Sexp = (sexp: any): Parsed4 | Error =>
    isEmpty(sexp) ? Error("Parse: Unexpected empty") :
    isArray(sexp) ? parseL4Compound(sexp) :
    isString(sexp) ? parseL3Atomic(sexp) :
    isSexpString(sexp) ? parseL3Atomic(sexp) :
    Error(`Parse: Unexpected type ${sexp}`);

const parseL4Compound = (sexps: any[]): Parsed4 | Error =>
    isEmpty(sexps) ? Error("Unexpected empty sexp") :
    (first(sexps) === "L4") ? parseProgram4(map(parseL4Sexp, rest(sexps))) :
    (first(sexps) === "define") ? parseDefine4(rest(sexps)) :
    parseL4CExp(sexps);

const parseProgram4 = (es: Array<Parsed4 | Error>): Program4 | Error =>
    isEmpty(es) ? Error("Empty program") :
    allT(isExp4, es) ? makeProgram4(es) :
    hasNoError(es) ? Error(`Program cannot be embedded in another program - ${es}`) :
    Error(getErrorMessages(es));

const parseDefine4 = (es: any[]): DefineExp4 | Error =>
    (es.length !== 2) ? Error(`define should be (define var val) - ${es}`) :
    !isString(es[0]) ? Error(`Expected (define <var> <CExp>) - ${es[0]}`) :
    safeF((val: CExp4) => makeDefineExp4(makeVarDecl(es[0]), val))(parseL4CExp(es[1]));

export const parseL4CExp = (sexp: any): CExp4 | Error =>
    isArray(sexp) ? parseL4CompoundCExp(sexp) :
    isString(sexp) ? parseL3Atomic(sexp) :
    isSexpString(sexp) ? parseL3Atomic(sexp) :
    Error("Unexpected type" + sexp);

const parseL4CompoundCExp = (sexps: any[]): CExp4 | Error =>
    isEmpty(sexps) ? Error("Unexpected empty") :
    first(sexps) === "if" ? parseIfExp4(sexps) :
    first(sexps) === "lambda" ? parseProcExp4(sexps) :
    first(sexps) === "let" ? parseLetExp4(sexps) :
    first(sexps) === "letrec" ? parseLetrecExp4(sexps) :
    first(sexps) === "set!" ? parseSetExp4(sexps) :
    first(sexps) === "quote" ? parseLitExp4(sexps) :
    parseAppExp4(sexps)

const parseAppExp4 = (sexps: any[]): AppExp4 | Error =>
    safeFL((cexps: CExp4[]) => makeAppExp4(first(cexps), rest(cexps)))(map(parseL4CExp, sexps));

const parseIfExp4 = (sexps: any[]): IfExp4 | Error =>
    safeFL((cexps: CExp4[]) => makeIfExp4(cexps[0], cexps[1], cexps[2]))(map(parseL4CExp, rest(sexps)));

const parseProcExp4 = (sexps: any[]): ProcExp4 | Error =>
    safeFL((body: CExp4[]) => makeProcExp4( map(makeVarDecl, sexps[1]), body))
        (map(parseL4CExp, rest(rest(sexps))));

// LetExp ::= (let (<binding>*) <cexp>+)
const parseLetExp4 = (sexps: any[]): LetExp4 | Error =>
    sexps.length < 3 ? Error(`Expected (let (<binding>*) <cexp>+) - ${sexps}`) :
    safeMakeLetExp4(parseBindings4(sexps[1]),
                    map(parseL4CExp, sexps.slice(2)));

const safeMakeLetExp4 = (bindings: Binding4[] | Error, body: Array<CExp4 | Error>): LetExp4 | Error =>
    isError(bindings) ? bindings :
    hasNoError(body) ? makeLetExp4(bindings, body) :
    Error(getErrorMessages(body));

const parseBindings4 = (pairs: any[]): Binding4[] | Error =>
    safeMakeBindings4(parseDecls(map(first, pairs)),
                      map(parseL4CExp, map(second, pairs)));

const safeMakeBindings4 = (decls: VarDecl[] | Error, vals: Array<CExp4 | Error>): Binding4[] | Error =>
    isError(decls) ? decls :
    hasNoError(vals) ? zipWith(makeBinding4, decls, vals) :
    Error(getErrorMessages(vals));

// LetrecExp ::= (letrec (<binding>*) <cexp>+)
const parseLetrecExp4 = (sexps: any[]): LetrecExp4 | Error =>
    sexps.length < 3 ? Error(`Expected (letrec (<binding>*) <cexp>+) - ${sexps}`) :
    safeMakeLetrecExp4(parseBindings4(sexps[1]),
                       map(parseL4CExp, sexps.slice(2)));

const safeMakeLetrecExp4 = (bindings: Binding4[] | Error, body: Array<CExp4 | Error>): LetrecExp4 | Error =>
    isError(bindings) ? bindings :
    hasNoError(body) ? makeLetrecExp4(bindings, body) :
    Error(getErrorMessages(body));

const parseSetExp4 = (es: any[]): SetExp4 | Error =>
    (es.length !== 2) ? Error(`set! should be (set! var val) - ${es}`) :
    !isString(es[0]) ? Error(`Expected (set! <var> <CExp>) - ${es[0]}`) :
    safeF((val: CExp4) => makeSetExp4(makeVarRef(es[0]), val))(parseL4CExp(es[1]));

export const parseLitExp4 = (sexps: any[]): LitExp4 | Error =>
    safeF(makeLitExp4)(parseSExp4(second(sexps)));

// x is the output of p (sexp parser)
export const parseSExp4 = (x: any): SExp4 | Error =>
    x === "#t" ? true :
    x === "#f" ? false :
    isNumericString(x) ? +x :
    isSexpString(x) ? x.toString() :
    isString(x) ? makeSymbolSExp(x) :
    x.length === 0 ? makeEmptySExp() :
    isArray(x) ? makeCompoundSExp4(map(parseSExp4, x)) :
    Error(`Bad literal expression: ${x}`);
