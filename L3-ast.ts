// ===========================================================
// AST type models
import * as assert from "assert";
import { filter, map, reduce, zipWith } from "ramda";
import { makeCompoundSExp, makeEmptySExp, makeSymbolSExp, SExp } from './L3-value'
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

;; <program> ::= (L3 <exp>+) // Program(exps:List(Exp))
;; <exp> ::= <define> | <cexp>              / DefExp | CExp
;; <define> ::= ( define <var> <cexp> )     / DefExp(var:VarDecl, val:CExp)
;; <var> ::= <identifier>                   / VarRef(var:string)
;; <cexp> ::= <number>                      / NumExp(val:number)
;;         |  <boolean>                     / BoolExp(val:boolean)
;;         |  <string>                      / StrExp(val:string)
;;         |  <varRef>                      / VarRef(var:string)
;;         |  ( lambda ( <var>* ) <cexp>+ ) / ProcExp(params:VarDecl[], body:CExp[]))
;;         |  ( if <cexp> <cexp> <cexp> )   / IfExp(test: CExp, then: CExp, alt: CExp)
;;         |  ( let ( binding* ) <cexp>+ )  / LetExp(bindings:Binding[], body:CExp[]))
;;         |  ( quote <sexp> )              / LitExp(val:SExp)
;;         |  ( <cexp> <cexp>* )            / AppExp(operator:CExp, operands:CExp[]))
;; <binding>  ::= ( <var> <cexp> )           / Binding(var:VarDecl, val:Cexp)
;; <prim-op>  ::= + | - | * | / | < | > | = | not |  eq? | string=?
;;                  | cons | car | cdr | list? | number?
;;                  | boolean? | symbol? | string?      ##### L3
;; <num-exp>  ::= a number token
;; <bool-exp> ::= #t | #f
;; <var-ref>  ::= an identifier token
;; <var-decl> ::= an identifier token
;; <sexp>     ::= symbol | number | bool | string | ( <sexp>* )              ##### L3
*/

// A value returned by parseL3
export type Parsed = Exp | Program;

export type Exp = DefineExp | CExp;
export type AtomicExp = NumExp | BoolExp | StrExp | PrimOp | VarRef;
export type CompoundExp = AppExp | IfExp | ProcExp | LetExp | LitExp;
export type CExp =  AtomicExp | CompoundExp;

export interface Program {tag: "Program"; exps: Exp[]; };
export interface DefineExp {tag: "DefineExp"; var: VarDecl; val: CExp; };
export interface NumExp {tag: "NumExp"; val: number; };
export interface BoolExp {tag: "BoolExp"; val: boolean; };
export interface StrExp {tag: "StrExp"; val: string; };
export interface PrimOp {tag: "PrimOp"; op: string; };
export interface VarRef {tag: "VarRef"; var: string; };
export interface VarDecl {tag: "VarDecl"; var: string; };
export interface AppExp {tag: "AppExp"; rator: CExp; rands: CExp[]; };
// L2
export interface IfExp {tag: "IfExp"; test: CExp; then: CExp; alt: CExp; };
export interface ProcExp {tag: "ProcExp"; args: VarDecl[], body: CExp[]; };
export interface Binding {tag: "Binding"; var: VarDecl; val: CExp; };
export interface LetExp {tag: "LetExp"; bindings: Binding[]; body: CExp[]; };
// L3
export interface LitExp {tag: "LitExp"; val: SExp; };

// Type value constructors for disjoint types
export const makeProgram = (exps: Exp[]): Program => ({tag: "Program", exps: exps});
export const makeDefineExp = (v: VarDecl, val: CExp): DefineExp =>
    ({tag: "DefineExp", var: v, val: val});
export const makeNumExp = (n: number): NumExp => ({tag: "NumExp", val: n});
export const makeBoolExp = (b: boolean): BoolExp => ({tag: "BoolExp", val: b});
export const makeStrExp = (s: string): StrExp => ({tag: "StrExp", val: s});
export const makePrimOp = (op: string): PrimOp => ({tag: "PrimOp", op: op});
export const makeVarRef = (v: string): VarRef => ({tag: "VarRef", var: v});
export const makeVarDecl = (v: string): VarDecl => ({tag: "VarDecl", var: v});
export const makeAppExp = (rator: CExp, rands: CExp[]): AppExp =>
    ({tag: "AppExp", rator: rator, rands: rands});
// L2
export const makeIfExp = (test: CExp, then: CExp, alt: CExp): IfExp =>
    ({tag: "IfExp", test: test, then: then, alt: alt});
export const makeProcExp = (args: VarDecl[], body: CExp[]): ProcExp =>
    ({tag: "ProcExp", args: args, body: body});
export const makeBinding = (v: VarDecl, val: CExp): Binding =>
    ({tag: "Binding", var: v, val: val});
export const makeLetExp = (bindings: Binding[], body: CExp[]): LetExp =>
    ({tag: "LetExp", bindings: bindings, body: body});
// L3
export const makeLitExp = (val: SExp): LitExp =>
    ({tag: "LitExp", val: val});

// Type predicates for disjoint types
export const isProgram = (x: any): x is Program => x.tag === "Program";
export const isDefineExp = (x: any): x is DefineExp => x.tag === "DefineExp";

export const isNumExp = (x: any): x is NumExp => x.tag === "NumExp";
export const isBoolExp = (x: any): x is BoolExp => x.tag === "BoolExp";
export const isStrExp = (x: any): x is StrExp => x.tag === "StrExp";
export const isPrimOp = (x: any): x is PrimOp => x.tag === "PrimOp";
export const isVarRef = (x: any): x is VarRef => x.tag === "VarRef";
export const isVarDecl = (x: any): x is VarDecl => x.tag === "VarDecl";
export const isAppExp = (x: any): x is AppExp => x.tag === "AppExp";
// L2
export const isIfExp = (x: any): x is IfExp => x.tag === "IfExp";
export const isProcExp = (x: any): x is ProcExp => x.tag === "ProcExp";
export const isBinding = (x: any): x is Binding => x.tag === "Binding";
export const isLetExp = (x: any): x is LetExp => x.tag === "LetExp";
// l3
export const isLitExp = (x: any): x is LitExp => x.tag === "LitExp";

// Type predicates for type unions
export const isExp = (x: any): x is Exp => isDefineExp(x) || isCExp(x);
export const isAtomicExp = (x: any): x is AtomicExp =>
    isNumExp(x) || isBoolExp(x) || isStrExp(x) ||
    isPrimOp(x) || isVarRef(x);
export const isCompoundExp = (x: any): x is CompoundExp =>
    isAppExp(x) || isIfExp(x) || isProcExp(x) || isLitExp(x) || isLetExp(x);
export const isCExp = (x: any): x is CExp =>
    isAtomicExp(x) || isCompoundExp(x);

// ========================================================
// Parsing utilities

export const isEmpty = (x: any): boolean => x.length === 0;
export const isArray = (x: any): boolean => x instanceof Array;
export const isString = (x: any): x is string => typeof x === "string";
export const isNumber = (x: any): x is number => typeof x === "number";
export const isBoolean = (x: any): x is boolean => typeof x === "boolean";

// s-expression returns strings quoted as "a" as [String: 'a'] objects
// to distinguish them from symbols - which are encoded as 'a'
// These are constructed using the new String("a") constructor
// and can be distinguished from regular strings based on the constructor.
export const isSexpString = (x: any): boolean =>
    ! isString(x) && x.constructor && x.constructor.name === "String";
// A weird method to check that a string is a string encoding of a number
export const isNumericString = (x: string): boolean => JSON.stringify(+x) === x;

// ========================================================
// Parsing

import p = require("s-expression");

export const parseL3 = (x: string): Parsed | Error =>
    parseL3Sexp(p(x));

export const parseL3Sexp = (sexp: any): Parsed | Error =>
    isEmpty(sexp) ? Error("Parse: Unexpected empty") :
    isArray(sexp) ? parseL3Compound(sexp) :
    isString(sexp) ? parseL3Atomic(sexp) :
    isSexpString(sexp) ? parseL3Atomic(sexp) :
    Error(`Parse: Unexpected type ${sexp}`);

const parseL3Compound = (sexps: any[]): Parsed | Error =>
    isEmpty(sexps) ? Error("Unexpected empty sexp") :
    (first(sexps) === "L3") ? parseProgram(map(parseL3Sexp, rest(sexps))) :
    (first(sexps) === "define") ? parseDefine(rest(sexps)) :
    parseL3CExp(sexps);

const parseProgram = (es: Array<Parsed | Error>): Program | Error =>
    isEmpty(es) ? Error("Empty program") :
    allT(isExp, es) ? makeProgram(es) :
    hasNoError(es) ? Error(`Program cannot be embedded in another program - ${es}`) :
    Error(getErrorMessages(es));

const parseDefine = (es: any[]): DefineExp | Error =>
    (es.length !== 2) ? Error(`define should be (define var val) - ${es}`) :
    !isString(es[0]) ? Error(`Expected (define <var> <CExp>) - ${es[0]}`) :
    safeF((val: CExp) => makeDefineExp(makeVarDecl(es[0]), val))(parseL3CExp(es[1]));

export const parseL3CExp = (sexp: any): CExp | Error =>
    isArray(sexp) ? parseL3CompoundCExp(sexp) :
    isString(sexp) ? parseL3Atomic(sexp) :
    isSexpString(sexp) ? parseL3Atomic(sexp) :
    Error("Unexpected type" + sexp);

const parseL3CompoundCExp = (sexps: any[]): CExp | Error =>
    isEmpty(sexps) ? Error("Unexpected empty") :
    first(sexps) === "if" ? parseIfExp(sexps) :
    first(sexps) === "lambda" ? parseProcExp(sexps) :
    first(sexps) === "let" ? parseLetExp(sexps) :
    first(sexps) === "quote" ? parseLitExp(sexps) :
    parseAppExp(sexps)

const parseAppExp = (sexps: any[]): AppExp | Error =>
    safeFL((cexps: CExp[]) => makeAppExp(first(cexps), rest(cexps)))(map(parseL3CExp, sexps));

const parseIfExp = (sexps: any[]): IfExp | Error =>
    safeFL((cexps: CExp[]) => makeIfExp(cexps[0], cexps[1], cexps[2]))(map(parseL3CExp, rest(sexps)));

const parseProcExp = (sexps: any[]): ProcExp | Error =>
    safeFL((body: CExp[]) => makeProcExp( map(makeVarDecl, sexps[1]), body))
        (map(parseL3CExp, rest(rest(sexps))));

export const parseDecls = (sexps: any[]): VarDecl[] | Error =>
    allT(isString, sexps) ? map(makeVarDecl, sexps) :
    Error(`VarDecl must be a string - ${sexps}`);

// LetExp ::= (let (<binding>*) <cexp>+)
const parseLetExp = (sexps: any[]): LetExp | Error =>
    sexps.length < 3 ? Error(`Expected (let (<binding>*) <cexp>+) - ${sexps}`) :
    safeMakeLetExp(parseBindings(sexps[1]),
                   map(parseL3CExp, sexps.slice(2)));

const safeMakeLetExp = (bindings: Binding[] | Error, body: Array<CExp | Error>): LetExp | Error =>
    isError(bindings) ? bindings :
    hasNoError(body) ? makeLetExp(bindings, body) :
    Error(getErrorMessages(body));

const parseBindings = (pairs: any[]): Binding[] | Error =>
    safeMakeBindings(parseDecls(map(first, pairs)),
                     map(parseL3CExp, map(second, pairs)));

const safeMakeBindings = (decls: VarDecl[] | Error, vals: Array<CExp | Error>): Binding[] | Error =>
    isError(decls) ? decls :
    hasNoError(vals) ? zipWith(makeBinding, decls, vals) :
    Error(getErrorMessages(vals));

export const parseL3Atomic = (sexp: string): AtomicExp =>
    sexp === "#t" ? makeBoolExp(true) :
    sexp === "#f" ? makeBoolExp(false) :
    isNumericString(sexp) ? makeNumExp(+sexp) :
    isSexpString(sexp) ? makeStrExp(sexp.toString()) :
    isPrimitiveOp(sexp) ? makePrimOp(sexp) :
    makeVarRef(sexp);

/*
    ;; <prim-op>  ::= + | - | * | / | < | > | = | not |  eq? | string=?
    ;;                  | cons | car | cdr | list? | number?
    ;;                  | boolean? | symbol? | string?      ##### L3
*/
const isPrimitiveOp = (x: string): boolean =>
    x === "+" ||
    x === "-" ||
    x === "*" ||
    x === "/" ||
    x === ">" ||
    x === "<" ||
    x === "=" ||
    x === "not" ||
    x === "eq?" ||
    x === "string=?" ||
    x === "cons" ||
    x === "car" ||
    x === "cdr" ||
    x === "list?" ||
    x === "number?" ||
    x === "boolean?" ||
    x === "symbol?" ||
    x === "string?";


export const parseLitExp = (sexps: any[]): LitExp | Error =>
    safeF(makeLitExp)(parseSExp(second(sexps)));

// x is the output of p (sexp parser)
export const parseSExp = (x: any): SExp | Error =>
    x === "#t" ? true :
    x === "#f" ? false :
    isNumericString(x) ? +x :
    isSexpString(x) ? x.toString() :
    isString(x) ? makeSymbolSExp(x) :
    x.length === 0 ? makeEmptySExp() :
    isArray(x) ? makeCompoundSExp(map(parseSExp, x)) :
    Error(`Bad literal expression: ${x}`);
