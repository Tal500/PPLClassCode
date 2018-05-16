import * as assert from "assert";
import { map } from 'ramda';
import { makeNumExp, parseL3, parseL3CExp } from './L3-ast';
import { makeVarDecl, makeVarRef } from './L3-ast';
import { isAppExp, isBoolExp, isCExp, isDefineExp, isIfExp, isLetExp, isLitExp, isNumExp, isPrimOp,
         isProcExp, isProgram, isStrExp, isVarDecl, isVarRef } from './L3-ast';
import { evalParse, renameExps, substitute  } from './L3-eval';
import { Value } from './L3-value';
import { makeClosure, makeCompoundSExp, makeEmptySExp, makeSymbolSExp } from './L3-value';
import { allT, first, second } from './list';

// ========================================================
// TESTS Parser

// Atomic
assert(isNumExp(parseL3("1")));
assert(isBoolExp(parseL3("#t")));
assert(isVarRef(parseL3("x")));
assert(isStrExp(parseL3('"a"')));
assert(isPrimOp(parseL3(">")));
assert(isPrimOp(parseL3("=")));
assert(isPrimOp(parseL3("string=?")));
assert(isPrimOp(parseL3("eq?")));
assert(isPrimOp(parseL3("cons")));

// Program
assert(isProgram(parseL3("(L3 (define x 1) (> (+ x 1) (* x x)))")));

// Define
assert(isDefineExp(parseL3("(define x 1)")));
{
    let def = parseL3("(define x 1)");
    if (isDefineExp(def)) {
        assert(isVarDecl(def.var));
        assert(isNumExp(def.val));
    }
}

// Application
assert(isAppExp(parseL3("(> x 1)")));
assert(isAppExp(parseL3("(> (+ x x) (* x x))")));

// L2 - If, Proc
assert(isIfExp(parseL3("(if #t 1 2)")));
assert(isIfExp(parseL3("(if (< x 2) x 2)")));
assert(isProcExp(parseL3("(lambda () 1)")));
assert(isProcExp(parseL3("(lambda (x) x x)")));

// L3 - Literal, Let
assert(isLetExp(parseL3("(let ((a 1) (b #t)) (if b a (+ a 1)))")));

assert(isLitExp(parseL3("'a")));
assert(isLitExp(parseL3("'()")));
assert(isLitExp(parseL3("'(1)")));

/*
console.log(parseL3("'a"));
console.log(parseL3("'\"b\""));
console.log(parseL3("'(s \"a\")"));
console.log(parseL3("'()"));
*/

// ========================================================
// Test L3 interpreter

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
assert.deepEqual(evalParse("(L3 (define x 1) (+ x x))"), 2);
assert.deepEqual(evalParse("(L3 (define x 1) (define y (+ x x)) (* y y))"), 4);

// Test if
assert.deepEqual(evalParse('(if (string? "a") 1 2)'), 1);
assert.deepEqual(evalParse('(if (not (string? "a")) 1 2)'), 2);

// Test proc
assert.deepEqual(evalParse("(lambda (x) x)"), makeClosure([makeVarDecl("x")], [makeVarRef("x")]));


// Test substitute
const es1 = map(parseL3, ["((lambda (x) (* x x)) x)"]);
if (allT(isCExp, es1))
    assert.deepEqual(substitute(es1, ["x"], [makeNumExp(3)]),
                     map(parseL3, ["((lambda (x) (* x x)) 3)"]));


// Replace n with 2 and f with (lambda (x) (* x x)) in e1:
const e1: string = `
  ((if (= n 0)
       (lambda (x) x)
       (if (= n 1)
           f
           (lambda (x) (f ((nf f (- n 1)) x)))))
   '(f n))`;
const vn = parseL3("2");
const vf = parseL3("(lambda (x) (* x x))");
// gives e2
const e2: string = `
  ((if (= 2 0)
       (lambda (x) x)
       (if (= 2 1)
           (lambda (x) (* x x))
           (lambda (x) ((lambda (x) (* x x))
                        ((nf (lambda (x) (* x x)) (- 2 1)) x)))))
       '(f n))`;
const es2 = map(parseL3, [e1, e2]);

// test
if (allT(isCExp, es2) && isCExp(vn) && isCExp(vf))
    assert.deepEqual(substitute([first(es2)], ["n", "f"], [vn, vf]),
                     [second(es2)]);

// Note how z becomes bound in the result of the substitution
// To avoid such accidental captures - we must use rename-vars.
const lzxz = parseL3("(lambda (z) (x z))");
const lwzw = parseL3("(lambda (w) (z w))");
// If you replace x with lwzw inside lzxz you obtain:
const lzlwzwz = parseL3("(lambda (z) ((lambda (w) (z w)) z))");

if (isCExp(lzxz) && isCExp(lwzw))
    assert.deepEqual(substitute([lzxz],
                                ["x"],
                                [lwzw]),
                     [lzlwzwz]);

// ========================================================
// Tests rename

const lxx = parseL3("(lambda (x) x)");
const lx1x1 = parseL3("(lambda (x__1) x__1)");
if (isCExp(lxx) && isCExp(lx1x1))
    assert.deepEqual(renameExps([lxx]), [lx1x1]);

const l1 = parseL3(
`(((lambda (x) (lambda (z) (x z)))
(lambda (w) (z w)))
2)`);
const rl1 = parseL3(
`(((lambda (x__1) (lambda (z__2) (x__1 z__2)))
       (lambda (w__3) (z w__3)))
      2)`);
if (isCExp(l1) && isCExp(rl1))
    assert.deepEqual(renameExps([l1]), [rl1]);

// Test apply proc
assert.deepEqual(evalParse("((lambda (x) (* x x)) 2)"), 4);
assert.deepEqual(evalParse("(L3 (define square (lambda (x) (* x x))) (square 3))"), 9);
assert.deepEqual(evalParse("(L3 (define f (lambda (x) (if (> x 0) x (- 0 x)))) (f -3))"), 3);
// Recursive procedure
assert.deepEqual(evalParse("(L3 (define f (lambda (x) (if (= x 0) 1 (* x (f (- x 1)))))) (f 3))"), 6);

// Preserve bound variables in subst
assert.deepEqual(evalParse(`
(L3 (define nf
            (lambda (f n)
                (if (= n 0)
                    (lambda (x) x)
                    (if (= n 1)
                        f
                        (lambda (x) (f ((nf f (- n 1)) x)))))))
    ((nf (lambda (x) (* x x)) 2) 3))`),
    81);

// Accidental capture of the z variable if no renaming
assert.deepEqual(evalParse(`
(L3
    (define z (lambda (x) (* x x)))
    (((lambda (x) (lambda (z) (x z)))
      (lambda (w) (z w)))
     2))`),
4);

// Y-combinator
assert.deepEqual(evalParse(`
(L3 (((lambda (f) (f f))
      (lambda (fact)
        (lambda (n)
          (if (= n 0)
              1
              (* n ((fact fact) (- n 1)))))))
     6))`),
    720);

// L3 higher order functions
assert.deepEqual(evalParse(`
(L3 (define map
            (lambda (f l)
              (if (eq? l '())
                  l
                  (cons (f (car l)) (map f (cdr l))))))
    (map (lambda (x) (* x x))
         '(1 2 3)))`),
    makeCompoundSExp([1, 4, 9]));

assert.deepEqual(evalParse(`
(L3 (define empty? (lambda (x) (eq? x '())))
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
(L3 (define compose (lambda (f g) (lambda (x) (f (g x)))))
    ((compose not number?) 2))`),
    false);

