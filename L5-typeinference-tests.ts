// L5-type-inference-tests-annotated
import * as assert from "assert";
import * as A from "./L5-ast";
import * as I from "./L5-typeinference";
import * as E from "./TEnv";
import * as T from "./TExp";
import { isError } from "./error";

export const verifyTeOfExpr = (exp: string, texp: string): boolean => {
    const e = A.parse(exp);
    if (A.isProgram(e)) {
        console.log("Program exps not yet supported");
        return false;
    }
    if (isError(e)) {
        console.log(`Bad expression ${exp} - ${e}`)
        return false;
    }
    const expectedType = T.parseTE(texp);
    if (isError(expectedType)) {
        console.log(`Bad expression ${texp} - ${expectedType}`)
        return false;
    }
    const computedType = I.typeofExp(e, E.makeEmptyTEnv());
    if (isError(computedType)) {
        console.log(`Type inference failed - expected ${texp} - ${computedType.message}`);
        return false;
    }
    const ok = T.equivalentTEs(computedType, expectedType);
    if (! ok) {
        console.log(`
Expected type ${T.unparseTExp(expectedType)}
Computed type: ${T.unparseTExp(computedType)}`);
    }
    return ok;
};

// type inference on annotated expressions

assert.deepEqual(I.inferTypeOf("5"), "number");
assert.deepEqual(I.inferTypeOf("#t"), "boolean");

assert.deepEqual(I.inferTypeOf("+"), "(number * number -> number)");
assert.deepEqual(I.inferTypeOf("-"), "(number * number -> number)");
assert.deepEqual(I.inferTypeOf("*"), "(number * number -> number)");
assert.deepEqual(I.inferTypeOf("/"), "(number * number -> number)");
assert.deepEqual(I.inferTypeOf("="), "(number * number -> boolean)");
assert.deepEqual(I.inferTypeOf("<"), "(number * number -> boolean)");
assert.deepEqual(I.inferTypeOf(">"), "(number * number -> boolean)");
assert.deepEqual(I.inferTypeOf("not"), "(boolean -> boolean)");

// typeof varref in a given TEnv
assert.deepEqual(I.typeofExp(A.parse("x"), E.makeExtendTEnv(["x"], [T.makeNumTExp()], E.makeEmptyTEnv())), T.makeNumTExp());

// IfExp
assert.deepEqual(I.inferTypeOf("(if (> 1 2) 1 2)"), "number");
assert.deepEqual(I.inferTypeOf("(if (= 1 2) #t #f)"), "boolean");

// ProcExp
assert.deepEqual(I.inferTypeOf("(lambda ((x : number)) : number x)"), "(number -> number)");
assert.deepEqual(I.inferTypeOf("(lambda ((x : number)) : boolean (> x 1))"), "(number -> boolean)");

assert.deepEqual(I.inferTypeOf("(lambda((x : number)) : (number -> number) (lambda((y : number)) : number (* y x)))"),
                 "(number -> (number -> number))");

assert.deepEqual(I.inferTypeOf("(lambda((f : (number -> number))) : number (f 2))"),
                 "((number -> number) -> number)");

assert.deepEqual(I.inferTypeOf(`(lambda((x : number)) : number
                                  (let (((y : number) x)) (+ x y)))`),
                 "(number -> number)");

// LetExp
assert.deepEqual(I.inferTypeOf("(let (((x : number) 1)) (* x 2))"), "number");

assert.deepEqual(I.inferTypeOf(`(let (((x : number) 1)
                                      ((y : number) 2))
                                   (lambda((a : number)) : number (+ (* x a) y)))`),
                 "(number -> number)");

// Letrec
assert.deepEqual(I.inferTypeOf(`(letrec (((p1 : (number -> number)) (lambda((x : number)) : number (* x x))))
                                  p1)`),
                 "(number -> number)");

assert.deepEqual(I.inferTypeOf(`(letrec (((p1 : (number -> number)) (lambda((x : number)) : number (* x x))))
                                  (p1 2))`),
                 "number");

assert.deepEqual(I.inferTypeOf(`(letrec (((odd? : (number -> boolean)) (lambda((n : number)) : boolean
                                                                    (if (= n 0) #f (even? (- n 1)))))
                                         ((even? : (number -> boolean)) (lambda((n : number)) : boolean
                                                                          (if (= n 0) #t (odd? (- n 1))))))
                                  (odd? 12))`),
                 "boolean");

// define
/*
assert.deepEqual(I.inferTypeOf("(define (foo : number) 5)"), "void");

assert.deepEqual(I.inferTypeOf("(define (foo : (number * number -> number)) (lambda((x : number) (y : number)) : number (+ x y)))"),
                 "void");
assert.deepEqual(I.inferTypeOf("(define (x : (Empty -> number)) (lambda () : number 1))"), "void");
*/

// Polymorphic tests
assert.deepEqual(I.inferTypeOf("(lambda((x : T1)) : T1 x)"), "(T1 -> T1)");

assert.deepEqual(I.inferTypeOf(`(let (((x : number) 1))
                             (lambda((y : T) (z : T)) : T
                               (if (> x 2) y z)))`),
                 "(T * T -> T)");

assert.deepEqual(I.inferTypeOf("(lambda () : number 1)"), "(Empty -> number)");

assert.deepEqual(I.inferTypeOf(`(define (x : (T1 -> (T1 -> number)))
                             (lambda ((x : T1)) : (T1 -> number)
                               (lambda((y : T1)) : number 5)))`), "void");


// Un-annotated expressions - "real" inference

console.log("Infer missing types\n=======================");

// Infer return type
assert(verifyTeOfExpr("(lambda ((x : number)) x)", "(number -> number)"));

// Infer param type
assert(verifyTeOfExpr('(lambda (x) : number x)', "(number -> number)"));

// Infer both param and return types
assert(verifyTeOfExpr('(lambda (x) (> x 1))', "(number -> boolean)"));

assert(verifyTeOfExpr('(lambda (x) (lambda (y) (* x y)))', "(number -> (number -> number))"));
assert(verifyTeOfExpr('(let ((x 1)) (* x 2))', "number"));

assert(verifyTeOfExpr(`
(let ((x 1)
      (y 2))
  (lambda (a) (+ (* x a) y)))`, "(number -> number)"));

assert(verifyTeOfExpr(`
(lambda (x)
  (let ((y x)) (+ x y)))`, "(number -> number)"));

assert(verifyTeOfExpr(`
(letrec ((p1 (lambda (x) (* x x))))
  p1)`, '(number -> number)'));

assert(verifyTeOfExpr(`
(letrec ((p1 (lambda (x) (* x x))))
  (p1 2))`, 'number'));

assert(verifyTeOfExpr(`
(letrec ((p1 (lambda (x) (* x x))))
  (p1 2))`, 'number'));

assert(verifyTeOfExpr('(lambda () 1)', "(Empty -> number)"));

assert(verifyTeOfExpr(`
(letrec ((p1 (lambda (x) (* x x))))
  (p1 2))`, 'number'));

assert(verifyTeOfExpr(`
(letrec ((odd? (lambda (n)
                  (if (= n 0) #f (even? (- n 1)))))
         (even? (lambda (n)
                  (if (= n 0) #t (odd? (- n 1))))))
    (odd? 12))`, 'boolean'));

// tests polymorphic unannotated
assert(verifyTeOfExpr(`(lambda (x) x)`, '(T1 -> T1)'));
assert(verifyTeOfExpr(`(lambda (f) (f 2))`, '((number -> T) -> T)'));
assert(verifyTeOfExpr(`
(let ((x 1))
  (lambda (y z) (if (> x 2) y z)))`, '(T * T -> T)'));

// this fails because our treatment of generics is limited
assert.deepEqual(verifyTeOfExpr(`
(letrec ((id (lambda (x) x)))
  (if (id #t) (id 1) (id 2)))`, "Error"), false);

