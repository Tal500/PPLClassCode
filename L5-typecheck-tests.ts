// L5-typecheck
import * as assert from "assert";
import { makeDefineExp, makeNumExp, makeProcExp, makeVarDecl, makeVarRef, parse } from './L5-ast';
import { typeofExp, L5typeof } from './L5-typecheck';
import { makeEmptyTEnv, makeExtendTEnv } from './TEnv';
import { makeBoolTExp, makeNumTExp, makeProcTExp, makeTVar, makeVoidTExp, parseTE, unparseTExp } from './TExp';

// parseTE
assert.deepEqual(parseTE("number"), makeNumTExp());
assert.deepEqual(parseTE("boolean"), makeBoolTExp());
assert.deepEqual(parseTE("T1"), makeTVar("T1"));
assert.deepEqual(parseTE("(T * T -> boolean)"), makeProcTExp([makeTVar("T"), makeTVar("T")], makeBoolTExp()));
assert.deepEqual(parseTE("(number -> (number -> number))"), makeProcTExp([makeNumTExp()], makeProcTExp([makeNumTExp()], makeNumTExp())));
assert.deepEqual(parseTE("void"), makeVoidTExp());
assert.deepEqual(parseTE("(Empty -> void)"), makeProcTExp([], makeVoidTExp()));

// unparseTExp
assert.deepEqual(unparseTExp(makeNumTExp()), "number");
assert.deepEqual(unparseTExp(makeBoolTExp()), "boolean");
assert.deepEqual(unparseTExp(makeTVar("T1")), "T1");
assert.deepEqual(unparseTExp(makeProcTExp([makeTVar("T"), makeTVar("T")], makeBoolTExp())), "(T * T -> boolean)");
assert.deepEqual(unparseTExp(makeProcTExp([makeNumTExp()], makeProcTExp([makeNumTExp()], makeNumTExp()))), "(number -> (number -> number))");

// parse with type annotations
assert.deepEqual(parse("(define (a : number) 1)"), makeDefineExp(makeVarDecl("a", makeNumTExp()), makeNumExp(1)));
assert.deepEqual(parse("(lambda ((x : number)) : number x)"),
                 makeProcExp([makeVarDecl("x", makeNumTExp())], [makeVarRef("x")], makeNumTExp()));

// L5typeof
assert.deepEqual(L5typeof("5"), "number");
assert.deepEqual(L5typeof("#t"), "boolean");

assert.deepEqual(L5typeof("+"), "(number * number -> number)");
assert.deepEqual(L5typeof("-"), "(number * number -> number)");
assert.deepEqual(L5typeof("*"), "(number * number -> number)");
assert.deepEqual(L5typeof("/"), "(number * number -> number)");
assert.deepEqual(L5typeof("="), "(number * number -> boolean)");
assert.deepEqual(L5typeof("<"), "(number * number -> boolean)");
assert.deepEqual(L5typeof(">"), "(number * number -> boolean)");
assert.deepEqual(L5typeof("not"), "(boolean -> boolean)");

// typeof varref in a given TEnv
assert.deepEqual(typeofExp(parse("x"), makeExtendTEnv(["x"], [makeNumTExp()], makeEmptyTEnv())), makeNumTExp());

// IfExp
assert.deepEqual(L5typeof("(if (> 1 2) 1 2)"), "number");
assert.deepEqual(L5typeof("(if (= 1 2) #t #f)"), "boolean");

// ProcExp
assert.deepEqual(L5typeof("(lambda ((x : number)) : number x)"), "(number -> number)");
assert.deepEqual(L5typeof("(lambda ((x : number)) : boolean (> x 1))"), "(number -> boolean)");

assert.deepEqual(L5typeof("(lambda((x : number)) : (number -> number) (lambda((y : number)) : number (* y x)))"),
                 "(number -> (number -> number))");

assert.deepEqual(L5typeof("(lambda((f : (number -> number))) : number (f 2))"),
                 "((number -> number) -> number)");

assert.deepEqual(L5typeof(`(lambda((x : number)) : number
                             (let (((y : number) x)) (+ x y)))`),
                 "(number -> number)");

// LetExp
assert.deepEqual(L5typeof("(let (((x : number) 1)) (* x 2))"), "number");

assert.deepEqual(L5typeof(`(let (((x : number) 1)
                                 ((y : number) 2))
                              (lambda((a : number)) : number (+ (* x a) y)))`),
                 "(number -> number)");

// Letrec
assert.deepEqual(L5typeof(`(letrec (((p1 : (number -> number)) (lambda((x : number)) : number (* x x))))
                             p1)`),
                 "(number -> number)");

assert.deepEqual(L5typeof(`(letrec (((p1 : (number -> number)) (lambda((x : number)) : number (* x x))))
                             (p1 2))`),
                 "number");

assert.deepEqual(L5typeof(`(letrec (((odd? : (number -> boolean)) (lambda((n : number)) : boolean
                                                                    (if (= n 0) #f (even? (- n 1)))))
                                    ((even? : (number -> boolean)) (lambda((n : number)) : boolean
                                                                     (if (= n 0) #t (odd? (- n 1))))))
                    (odd? 12))`),
                 "boolean");

// define
assert.deepEqual(L5typeof("(define (foo : number) 5)"), "void");

assert.deepEqual(L5typeof("(define (foo : (number * number -> number)) (lambda((x : number) (y : number)) : number (+ x y)))"),
                 "void");
assert.deepEqual(L5typeof("(define (x : (Empty -> number)) (lambda () : number 1))"), "void");

/*
// LitExp
assert.deepEqual(L5typeof("(quote ())"), "literal");

// Pair
assert.deepEqual(L5typeof("(cons 1 '())"), "(Pair number literal)");
assert.deepEqual(L5typeof("(cons 1 1)"), "(Pair number number)");
assert.deepEqual(L5typeof("(car (cons 1 1))"), "number");
 assert.deepEqual(L5typeof("(cdr (cons 1 #t))"), "boolean");
 assert.deepEqual(L5typeof("(cdr (cons (cons 1 2) (cons 1 2)))"), "(Pair number number)");
 assert.deepEqual(L5typeof("(cdr (cons (cons 1 2) (cons 1 #f)))"), "(Pair number boolean)");
 assert.deepEqual(L5typeof("(car (cons (cons 1 2) (cons 1 #f)))"), "(Pair number number)");
 assert.deepEqual(L5typeof("(car (cons (cons (cons #t #t) 2) (cons 1 #f)))"), "(Pair (Pair boolean boolean) number)");
 assert.deepEqual(L5typeof("(cdr (cons (cons (cons #t #t) 2) (cons 1 #f)))"), "(Pair number boolean)");
 assert.deepEqual(L5typeof("(lambda((a : number) (b : number)) : (Pair number number) (cons a b))"),
            ,     "(number * number -> (Pair number number))");
 assert.deepEqual(L5typeof("(lambda((a : number) (b : (Pair number boolean))) : (Pair number (Pair number boolean)) (cons a b))"),
                  "(number * (Pair number boolean) -> (Pair number (Pair number boolean)))");
 assert.deepEqual(L5typeof(`(lambda((a : (Pair number number))
                                    (b : (Pair number boolean))) :
                                    (Pair (Pair number number) (Pair (Pair number number) (Pair number boolean)))
                              (cons a (cons a b)))"),
            "((Pair number number) * (Pair number boolean) -> (Pair (Pair number number) (Pair (Pair number number) (Pair number boolean))))");


assert.deepEqual(L5typeof("(define (x : (Pair number boolean)) (cons 1 #t))"), "void");
assert.deepEqual(L5typeof("(define (x : (Pair (T1 -> T1) number)) (cons (lambda ((y : T1)) : T1 y) 2))"), "void");

*/

// Polymorphic tests
assert.deepEqual(L5typeof("(lambda((x : T1)) : T1 x)"), "(T1 -> T1)");

assert.deepEqual(L5typeof(`(let (((x : number) 1))
                             (lambda((y : T) (z : T)) : T
                               (if (> x 2) y z)))`),
                 "(T * T -> T)");

assert.deepEqual(L5typeof("(lambda () : number 1)"), "(Empty -> number)");

assert.deepEqual(L5typeof(`(define (x : (T1 -> (T1 -> number)))
                             (lambda ((x : T1)) : (T1 -> number)
                               (lambda((y : T1)) : number 5)))`), "void");
