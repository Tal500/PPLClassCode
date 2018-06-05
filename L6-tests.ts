import * as assert from "assert";
import { map } from 'ramda';
import { makeNumExp, makeVarDecl, makeVarRef } from './L5-ast';
import { isBoolExp, isNumExp, isPrimOp, isStrExp, isVarDecl, isVarRef } from './L5-ast';
import { parse, unparse } from './L5-ast';
import { isAppExp, isCExp, isDefineExp, isIfExp, isLetrecExp, isLetExp,
         isLitExp, isProcExp, isProgram, isSetExp } from './L5-ast';
import { applyEnv, globalEnvAddBinding, theGlobalEnv } from "./L5-env";
import { makeEmptySExp, makeSymbolSExp } from './L5-value';
import { isClosure, makeClosure, makeCompoundSExp, Value } from './L5-value';
import { evalParse } from './L6-eval';
import { isError } from './error';
import { allT, first, second } from './list';

// ========================================================
// TESTS Parser

// Atomic
assert(isNumExp(parse("1")));
assert(isBoolExp(parse("#t")));
assert(isVarRef(parse("x")));
assert(isStrExp(parse('"a"')));
assert(isPrimOp(parse(">")));
assert(isPrimOp(parse("=")));
assert(isPrimOp(parse("string=?")));
assert(isPrimOp(parse("eq?")));
assert(isPrimOp(parse("cons")));

// Program
assert(isProgram(parse("(L5 (define x 1) (> (+ x 1) (* x x)))")));

// Define
assert(isDefineExp(parse("(define x 1)")));
{
    let def = parse("(define x 1)");
    if (isDefineExp(def)) {
        assert(isVarDecl(def.var));
        assert(isNumExp(def.val));
    }
}

// Application
assert(isAppExp(parse("(> x 1)")));
assert(isAppExp(parse("(> (+ x x) (* x x))")));

// L2 - If, Proc
assert(isIfExp(parse("(if #t 1 2)")));
assert(isIfExp(parse("(if (< x 2) x 2)")));
assert(isProcExp(parse("(lambda () 1)")));
assert(isProcExp(parse("(lambda (x) x x)")));

// L3 - Literal, Let
assert(isLetExp(parse("(let ((a 1) (b #t)) (if b a (+ a 1)))")));

assert(isLitExp(parse("'a")));
assert(isLitExp(parse("'()")));
assert(isLitExp(parse("'(1)")));

// L3 - Literal, Let
assert(isLetExp(parse("(let ((a 1) (b #t)) (if b a (+ a 1)))")));

// L4 - letrec
assert(isLetrecExp(parse("(letrec ((e (lambda (x) x))) (e 2))")));
assert(isSetExp(parse("(set! x 1)")));

// L5 type annotations and unparse

// L5 unparse
const e1 = "(define (a : number) 1)";
const e2 = "(lambda ((x : number)) : number (* x x))";
const e3 = "(let (((a : boolean) #t) ((b : number) 2)) (if a b (+ b b)))";
const e4 = `(letrec (((p : (number * number -> number)) (lambda ((x : number) (y : number)) (+ x y)))) (p 1 2))`;

[e1, e2, e3, e4].forEach((e) => assert.deepEqual(unparse(parse(e)), e));

assert(isDefineExp(parse(e1)));
assert(isProcExp(parse(e2)));
assert(isLetExp(parse(e3)));
assert(isLetrecExp(parse(e4)));

/*
console.log(parse("'a"));
console.log(parse("'\"b\""));
console.log(parse("'(s \"a\")"));
console.log(parse("'()"));
*/

// ========================================================
// Test L5 Box interpreter

// ========================================================
// TESTS GlobalEnv
// globalEnvAddBinding("m", 1);
// assert.deepEqual(applyEnv(theGlobalEnv, "m"), 1);

// ========================================================
// TESTS

// Test each data type literals
assert.deepEqual(evalParse("1"), 1);
assert.deepEqual(evalParse("#t"), true);
assert.deepEqual(evalParse("#f"), false);
assert.deepEqual(evalParse("'a"), makeSymbolSExp("a"));
assert.deepEqual(evalParse('"a"'), "a");
assert.deepEqual(evalParse("'()"), makeEmptySExp());
assert.deepEqual(evalParse("'(1 2)"), makeCompoundSExp([1, 2]));
assert.deepEqual(evalParse("'(1 (2))"), makeCompoundSExp([1, makeCompoundSExp([2])]));

// Test primitives
/*
;; <prim-op>  ::= + | - | * | / | < | > | = | not |  eq? | string=?
;;                  | cons | car | cdr | list? | number?
;;                  | boolean? | symbol? | string?      ##### L3
*/
assert.deepEqual(evalParse("(+ 1 2)"), 3);
assert.deepEqual(evalParse("(- 2 1)"), 1);
assert.deepEqual(evalParse("(* 2 3)"), 6);
assert.deepEqual(evalParse("(/ 4 2)"), 2);
assert.deepEqual(evalParse("(< 4 2)"), false);
assert.deepEqual(evalParse("(> 4 2)"), true);
assert.deepEqual(evalParse("(= 4 2)"), false);
assert.deepEqual(evalParse("(not #t)"), false);
assert.deepEqual(evalParse("(eq? 'a 'a)"), true);
assert.deepEqual(evalParse('(string=? "a" "a")'), true);
assert.deepEqual(evalParse("(cons 1 '())"), makeCompoundSExp([1]));
assert.deepEqual(evalParse("(cons 1 '(2))"), makeCompoundSExp([1, 2]));
assert.deepEqual(evalParse("(car '(1 2))"), 1);
assert.deepEqual(evalParse("(cdr '(1 2))"), makeCompoundSExp([2]));
assert.deepEqual(evalParse("(cdr '(1))"), makeEmptySExp());
assert.deepEqual(evalParse("(list? '(1))"), true);
assert.deepEqual(evalParse("(list? '())"), true);
assert.deepEqual(evalParse("(number? 1)"), true);
assert.deepEqual(evalParse("(number? #t)"), false);
assert.deepEqual(evalParse("(boolean? #t)"), true);
assert.deepEqual(evalParse("(boolean? 0)"), false);
assert.deepEqual(evalParse("(symbol? 'a)"), true);
assert.deepEqual(evalParse('(symbol? "a")'), false);
assert.deepEqual(evalParse("(string? 'a)"), false);
assert.deepEqual(evalParse('(string? "a")'), true);

// Test define
assert.deepEqual(evalParse("(L5 (define x 1) (+ x x))"), 2);
assert.deepEqual(evalParse("(L5 (define x 1) (define y (+ x x)) (* y y))"), 4);

// Test if
assert.deepEqual(evalParse('(if (string? "a") 1 2)'), 1);
assert.deepEqual(evalParse('(if (not (string? "a")) 1 2)'), 2);

// Test proc
// Closures include TVars with unpredictable numbers - test types instead.
{
    let cl1 = evalParse("(lambda (x) x)");
    if (isClosure(cl1)) {
        assert(isVarDecl(cl1.params[0]));
        assert(isVarRef(cl1.body[0]));
    } else {
        console.error(`Bad closure ${cl1}`);
    }
}

// Test apply proc
assert.deepEqual(evalParse("((lambda (x) (* x x)) 2)"), 4);
assert.deepEqual(evalParse("(L5 (define square (lambda (x) (* x x))) (square 3))"), 9);
assert.deepEqual(evalParse("(L5 (define f (lambda (x) (if (> x 0) x (- 0 x)))) (f -3))"), 3);

// L4 BOX
// Recursive procedure = WORKS as in Scheme
assert.deepEqual(evalParse("(L5 (define f (lambda (x) (if (= x 0) 1 (* x (f (- x 1)))))) (f 3))"), 6);

// Recursion with letrec
assert.deepEqual(evalParse(`
(letrec ((f (lambda (n) (if (= n 0) 1 (* n (f (- n 1)))))))
  (f 5))
`), 120);

// Preserve bound variables
assert.deepEqual(evalParse(`
(L5 (define fact
        (letrec ((f (lambda (n)
                      (if (= n 0)
                          1
                          (* n (f (- n 1)))))))
          f))
    (fact 5))
`), 120);

// Accidental capture of the z variable if no renaming - works without renaming in env eval.
assert.deepEqual(evalParse(`
(L5
    (define z (lambda (x) (* x x)))
    (((lambda (x) (lambda (z) (x z)))
      (lambda (w) (z w)))
     2))`),
4);

// Y-combinator
assert.deepEqual(evalParse(`
(L5 (((lambda (f) (f f))
      (lambda (fact)
        (lambda (n)
          (if (= n 0)
              1
              (* n ((fact fact) (- n 1)))))))
     6))`),
    720);

// L4 higher order functions
assert.deepEqual(evalParse(`
(L5 (define map
      (lambda (f l)
        (if (eq? l '())
          l
          (cons (f (car l)) (map f (cdr l))))))
    (map (lambda (x) (* x x))
      '(1 2 3)))`),
    makeCompoundSExp([1, 4, 9]));

assert.deepEqual(evalParse(`
(L5 (define empty? (lambda (x) (eq? x '())))
    (define filter
      (lambda (pred l)
        (if (empty? l)
          l
          (if (pred (car l))
              (cons (car l) (filter pred (cdr l)))
              (filter pred (cdr l))))))
    (filter (lambda (x) (not (= x 2)))
        '(1 2 3 2)))`),
    makeCompoundSExp([1, 3]));

assert.deepEqual(evalParse(`
(L5 (define compose (lambda (f g) (lambda (x) (f (g x)))))
    ((compose not number?) 2))`),
    false);

// @@ Properly capture variables in closures
assert.deepEqual(evalParse(`
(L5 (define makeAdder (lambda (n) (lambda (y) (+ y n))))
    (define a6 (makeAdder 6))
    (define a7 (makeAdder 7))
    (+ (a6 1) (a7 1)))
    `),
    15);

assert.deepEqual(evalParse(`
(L5 (define makeCounter (lambda () (let ((c 0)) (lambda () (set! c (+ c 1)) c))))
    (define c1 (makeCounter))
    (define c2 (makeCounter))
    (+ (+ (c1) (c1))
       (+ (c2) (c2))))
    `),
    6);

// L5 eval with type annotations

assert.deepEqual(evalParse("(L5 (define (a : number) 1) a)"), 1);

assert.deepEqual(evalParse("((lambda ((x : T)) : T x) #t)"), true);

assert.deepEqual(evalParse("(let (((a : boolean) #t) ((b : number) 2)) (if a b (+ b b)))"), 2);

assert.deepEqual(evalParse(`
    (letrec (((p : (number * number -> number)) (lambda ((x : number) (y : number)) (+ x y))))
        (p 1 2))
    `), 3);
