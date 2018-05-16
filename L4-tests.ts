import * as assert from "assert";
import { map } from 'ramda';
import { makeNumExp, makeVarDecl, makeVarRef } from './L3-ast';
import { isBoolExp, isNumExp, isPrimOp, isStrExp, isVarDecl, isVarRef } from './L3-ast';
import { makeEmptySExp, makeSymbolSExp } from './L3-value';
import { isAppExp4, isCExp4, isDefineExp4, isIfExp4, isLetrecExp4, isLetExp4, isLitExp4, isProcExp4, isProgram4 } from './L4-ast';
import { parseL4, parseL4CExp } from './L4-ast';
import { makeEmptyEnv } from "./L4-env";
import { evalParse4 } from './L4-eval';
import { Value4 } from './L4-value';
import { makeClosure4, makeCompoundSExp4 } from './L4-value';
import { isError } from './error';
import { allT, first, second } from './list';

// ========================================================
// TESTS Parser

// Atomic
assert(isNumExp(parseL4("1")));
assert(isBoolExp(parseL4("#t")));
assert(isVarRef(parseL4("x")));
assert(isStrExp(parseL4('"a"')));
assert(isPrimOp(parseL4(">")));
assert(isPrimOp(parseL4("=")));
assert(isPrimOp(parseL4("string=?")));
assert(isPrimOp(parseL4("eq?")));
assert(isPrimOp(parseL4("cons")));

// Program
assert(isProgram4(parseL4("(L4 (define x 1) (> (+ x 1) (* x x)))")));

// Define
assert(isDefineExp4(parseL4("(define x 1)")));
{
    let def = parseL4("(define x 1)");
    if (isDefineExp4(def)) {
        assert(isVarDecl(def.var));
        assert(isNumExp(def.val));
    }
}

// Application
assert(isAppExp4(parseL4("(> x 1)")));
assert(isAppExp4(parseL4("(> (+ x x) (* x x))")));

// L2 - If, Proc
assert(isIfExp4(parseL4("(if #t 1 2)")));
assert(isIfExp4(parseL4("(if (< x 2) x 2)")));
assert(isProcExp4(parseL4("(lambda () 1)")));
assert(isProcExp4(parseL4("(lambda (x) x x)")));

// L3 - Literal, Let
assert(isLetExp4(parseL4("(let ((a 1) (b #t)) (if b a (+ a 1)))")));

assert(isLitExp4(parseL4("'a")));
assert(isLitExp4(parseL4("'()")));
assert(isLitExp4(parseL4("'(1)")));

// L3 - Literal, Let
assert(isLetExp4(parseL4("(let ((a 1) (b #t)) (if b a (+ a 1)))")));

// L4 - letrec
assert(isLetrecExp4(parseL4("(letrec ((e (lambda (x) x))) (e 2))")));

/*
console.log(parseL4("'a"));
console.log(parseL4("'\"b\""));
console.log(parseL4("'(s \"a\")"));
console.log(parseL4("'()"));
*/

// ========================================================
// Test L4 interpreter

// ========================================================
// TESTS

// Test each data type literals
assert.deepEqual(evalParse4("1"), 1);
assert.deepEqual(evalParse4("#t"), true);
assert.deepEqual(evalParse4("#f"), false);
assert.deepEqual(evalParse4("'a"), makeSymbolSExp("a"));
assert.deepEqual(evalParse4('"a"'), "a");
assert.deepEqual(evalParse4("'()"), makeEmptySExp());
assert.deepEqual(evalParse4("'(1 2)"), makeCompoundSExp4([1, 2]));
assert.deepEqual(evalParse4("'(1 (2))"), makeCompoundSExp4([1, makeCompoundSExp4([2])]));

// Test primitives
/*
;; <prim-op>  ::= + | - | * | / | < | > | = | not |  eq? | string=?
;;                  | cons | car | cdr | list? | number?
;;                  | boolean? | symbol? | string?      ##### L3
*/
assert.deepEqual(evalParse4("(+ 1 2)"), 3);
assert.deepEqual(evalParse4("(- 2 1)"), 1);
assert.deepEqual(evalParse4("(* 2 3)"), 6);
assert.deepEqual(evalParse4("(/ 4 2)"), 2);
assert.deepEqual(evalParse4("(< 4 2)"), false);
assert.deepEqual(evalParse4("(> 4 2)"), true);
assert.deepEqual(evalParse4("(= 4 2)"), false);
assert.deepEqual(evalParse4("(not #t)"), false);
assert.deepEqual(evalParse4("(eq? 'a 'a)"), true);
assert.deepEqual(evalParse4('(string=? "a" "a")'), true);
assert.deepEqual(evalParse4("(cons 1 '())"), makeCompoundSExp4([1]));
assert.deepEqual(evalParse4("(cons 1 '(2))"), makeCompoundSExp4([1, 2]));
assert.deepEqual(evalParse4("(car '(1 2))"), 1);
assert.deepEqual(evalParse4("(cdr '(1 2))"), makeCompoundSExp4([2]));
assert.deepEqual(evalParse4("(cdr '(1))"), makeEmptySExp());
assert.deepEqual(evalParse4("(list? '(1))"), true);
assert.deepEqual(evalParse4("(list? '())"), true);
assert.deepEqual(evalParse4("(number? 1)"), true);
assert.deepEqual(evalParse4("(number? #t)"), false);
assert.deepEqual(evalParse4("(boolean? #t)"), true);
assert.deepEqual(evalParse4("(boolean? 0)"), false);
assert.deepEqual(evalParse4("(symbol? 'a)"), true);
assert.deepEqual(evalParse4('(symbol? "a")'), false);
assert.deepEqual(evalParse4("(string? 'a)"), false);
assert.deepEqual(evalParse4('(string? "a")'), true);

// Test define
assert.deepEqual(evalParse4("(L4 (define x 1) (+ x x))"), 2);
assert.deepEqual(evalParse4("(L4 (define x 1) (define y (+ x x)) (* y y))"), 4);

// Test if
assert.deepEqual(evalParse4('(if (string? "a") 1 2)'), 1);
assert.deepEqual(evalParse4('(if (not (string? "a")) 1 2)'), 2);

// Test proc
assert.deepEqual(evalParse4("(lambda (x) x)"), makeClosure4([makeVarDecl("x")], [makeVarRef("x")], makeEmptyEnv()));


// Test apply proc
assert.deepEqual(evalParse4("((lambda (x) (* x x)) 2)"), 4);
assert.deepEqual(evalParse4("(L4 (define square (lambda (x) (* x x))) (square 3))"), 9);
assert.deepEqual(evalParse4("(L4 (define f (lambda (x) (if (> x 0) x (- 0 x)))) (f -3))"), 3);

// Recursive procedure = does not work with ExtEnv - requires RecEnv!
// message: 'Error: Bad argument: "var not found f"'
assert(isError(evalParse4("(L4 (define f (lambda (x) (if (= x 0) 1 (* x (f (- x 1)))))) (f 3))")));

// Recursion with letrec
assert.deepEqual(evalParse4(`
(letrec ((f (lambda (n) (if (= n 0) 1 (* n (f (- n 1)))))))
  (f 5))
`), 120);

// Preserve bound variables
assert.deepEqual(evalParse4(`
(L4 (define fact
        (letrec ((f (lambda (n)
                      (if (= n 0)
                          1
                          (* n (f (- n 1)))))))
          f))
    (fact 5))
`), 120);

// Accidental capture of the z variable if no renaming - works without renaming in env eval.
assert.deepEqual(evalParse4(`
(L4
    (define z (lambda (x) (* x x)))
    (((lambda (x) (lambda (z) (x z)))
      (lambda (w) (z w)))
     2))`),
4);

// Y-combinator
assert.deepEqual(evalParse4(`
(L4 (((lambda (f) (f f))
      (lambda (fact)
        (lambda (n)
          (if (= n 0)
              1
              (* n ((fact fact) (- n 1)))))))
     6))`),
    720);

// L4 higher order functions
assert.deepEqual(evalParse4(`
(L4 (define map
      (letrec ((map (lambda (f l)
                      (if (eq? l '())
                          l
                          (cons (f (car l)) (map f (cdr l)))))))
         map))
    (map (lambda (x) (* x x))
      '(1 2 3)))`),
    makeCompoundSExp4([1, 4, 9]));

assert.deepEqual(evalParse4(`
(L4 (define empty? (lambda (x) (eq? x '())))
    (define filter
        (letrec ((filter (lambda (pred l)
                       (if (empty? l)
                           l
                           (if (pred (car l))
                               (cons (car l) (filter pred (cdr l)))
                               (filter pred (cdr l)))))))
            filter))
    (filter (lambda (x) (not (= x 2)))
        '(1 2 3 2)))`),
    makeCompoundSExp4([1, 3]));

assert.deepEqual(evalParse4(`
(L4 (define compose (lambda (f g) (lambda (x) (f (g x)))))
    ((compose not number?) 2))`),
    false);

