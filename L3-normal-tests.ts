// ========================================================
// Normal eval tests
import * as assert from "assert";
import { map } from 'ramda';
import { makeNumExp, parseL3 } from './L3-ast';
import { makePrimOp, makeVarDecl, makeVarRef } from './L3-ast';
import { isAppExp, isBoolExp, isDefineExp, isIfExp, isLetExp, isLitExp, isNumExp, isPrimOp,
         isProcExp, isProgram, isStrExp, isVarDecl, isVarRef } from './L3-ast';
import { makeEmptyEnv } from './L3-env';
import { evalNormalParse, L3normalEval } from './L3-normal';
import { Value } from './L3-value';
import { isClosure, makeClosure, makeCompoundSExp, makeEmptySExp, makeSymbolSExp } from './L3-value';

const ge = makeEmptyEnv();
assert.equal(evalNormalParse("1"), 1);
assert.equal(evalNormalParse("#t"), true);
assert.deepEqual(evalNormalParse("+"), makePrimOp("+"));
assert.equal(evalNormalParse("(+ 1 2)"), 3);
assert.equal(evalNormalParse("(< 1 2)"), true);
assert.equal(evalNormalParse("(not (> 1 2))"), true);
assert.equal(evalNormalParse("(+ (* 2 2) 3)"), 7);

// L2 syntactic forms
assert.equal(evalNormalParse("(if (< 1 2) 3 -3)"), 3);
assert(isClosure(evalNormalParse("(lambda (x) x)")));

// L3 syntactic forms
assert.deepEqual(evalNormalParse("(cons 1 '())"), makeCompoundSExp([1]));
assert.equal(evalNormalParse("(car '(1 2))"), 1);
assert.deepEqual(evalNormalParse("(cdr '(1 2))"), makeCompoundSExp([2]));
assert.equal(evalNormalParse("(number? 'x)"), false);
assert.equal(evalNormalParse("(number? 1)"), true);
assert.equal(evalNormalParse("(symbol? 'x)"), true);
assert.equal(evalNormalParse("(symbol? 1)"), false);
assert.equal(evalNormalParse("(list? 1)"), false);
assert.equal(evalNormalParse("(list? '(1 2))"), true);
assert.equal(evalNormalParse("(boolean? 1)"), false);
assert.equal(evalNormalParse("(boolean? #t)"), true);
assert.equal(evalNormalParse("(eq? 'x 'x)"), true);

// Program
assert.equal(evalNormalParse(`(L3 (define x (+ 3 2))
                                  (* x x))`),
                             25);
assert.equal(evalNormalParse(`(L3 (define x (+ 3 2))
                                  (* x x)
                                  (+ x x))`),
                        10);

// Procedure application
assert.equal(evalNormalParse(`(L3 (define f (lambda (x) (* x x))) (f 3))`),
             9);
assert.equal(evalNormalParse(`(L3 (define f (lambda (x) (if (> x 0) x (- 0 x)))) (f -3))`),
             3);

// Recursive procedure
assert.equal(evalNormalParse(`
(L3
    (define f (lambda (x) (if (= x 0)
                              1
                              (* x (f (- x 1))))))
    (f 5))`),
120);

// TODO     (test (normal-L3-program (parseL3 '(L3 (define x 1)))) => (void))


// Preserve bound variables in subst
assert.equal(evalNormalParse(`
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
assert.equal(evalNormalParse(`
(L3
    (define z (lambda (x) (* x x)))
    (((lambda (x) (lambda (z) (x z)))
        (lambda (w) (z w)))
    2))`),
4);

// Y-combinator
assert.equal(evalNormalParse(`
(L3 (((lambda (f) (f f))
        (lambda (fact)
            (lambda (n)
                (if (= n 0)
                    1
                    (* n ((fact fact) (- n 1)))))))
    6))`),
720);

// L3 higher order functions
assert.deepEqual(evalNormalParse(`
(L3 (define map
        (lambda (f l)
            (if (eq? l '())
                l
                (cons (f (car l)) (map f (cdr l))))))
    (map (lambda (x) (* x x))
        '(1 2 3)))`),
makeCompoundSExp([1, 4, 9]));

assert.deepEqual(evalNormalParse(`
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

assert.equal(evalNormalParse(`
(L3 (define compose (lambda (f g) (lambda (x) (f (g x)))))
    ((compose not number?) 2))`),
false);

// Normal only tests
// These programs behave differently under normal evaluation than applicative

// This program loops in eval-order - but completes in normal order
assert.equal(evalNormalParse(`
(L3 (define loop (lambda () (loop)))
    (define f (lambda (x y z) (if (= x 1) y z)))
    (f 1 2 (loop)))`),
2);

// This program loops in eval-order - but completes in normal order
assert.equal(evalNormalParse(`
(L3
    (define loop (lambda (x) (loop x)))
    (define g (lambda (x) 5))
    (g (loop 0)))`),
5);

assert.equal(evalNormalParse(`
(L3
    (define try
        (lambda (a b)
        (if (= a 0)
            1
            b)))
    (try 0 (/ 1 0)))`),
1);

assert.equal(evalNormalParse(`
(L3
    (define f (lambda (x) (display x) (newline) (+ x 1)))
    (define g (lambda (x) 5))
    (g (f 0)))`),
5);
