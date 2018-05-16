import * as assert from "assert";
import { makeVarRef, parseL3 } from './L3-ast';
import { height, occursFree, referencedVars } from './freeVars';

assert.deepEqual(height(parseL3("x")), 1);
assert.deepEqual(height(parseL3("(lambda (x) (* x x))")), 2);

assert.equal(occursFree("x", parseL3("1")), false);
assert.equal(occursFree("x", parseL3("#t")), false);
assert.equal(occursFree("x", parseL3('"s"')), false);
assert.equal(occursFree("x", parseL3("'s")), false);
assert.equal(occursFree("x", parseL3("x")), true);
assert.equal(occursFree("x", parseL3("y")), false);

assert.equal(occursFree("x", parseL3("(lambda () x)")), true);
assert.equal(occursFree("x", parseL3("(lambda (x) x)")), false);
assert.equal(occursFree("x", parseL3("(lambda (y) x)")), true);
assert.equal(occursFree("x", parseL3("(lambda (y) (lambda (z) x))")), true);
assert.equal(occursFree("x", parseL3("(lambda (x) (lambda (z) x))")), false);
assert.equal(occursFree("x", parseL3("(lambda (y x) x)")), false);

assert.equal(occursFree("x", parseL3("(if x 1 2)")), true);
assert.equal(occursFree("x", parseL3("(if #t x 2)")), true);
assert.equal(occursFree("x", parseL3("(if #t 1 x)")), true);
assert.equal(occursFree("x", parseL3("(if #t 1 2)")), false);

assert.equal(occursFree("x", parseL3("(+ 1 x)")), true);
assert.equal(occursFree("x", parseL3("(+ 1 2)")), false);

/*
assert.equal(occursFree("x", parseL3("(let () x)")), true);
assert.equal(occursFree("x", parseL3("(let ((x 1)) x)")), false);
assert.equal(occursFree("x", parseL3("(let ((y 1)) x)")), true);
assert.equal(occursFree("x", parseL3("(let ((y 1)) (lambda (z) x))")), true);
assert.equal(occursFree("x", parseL3("(let ((x 1)) (lambda (z) x))")), false);
assert.equal(occursFree("x", parseL3("(let ((y 1) (x 2)) x)")), false);
assert.equal(occursFree("x", parseL3("(let ((y x) (x 2)) x)")), true);
assert.equal(occursFree("x", parseL3("(let ((y x) (x 2)) z)")), true);
*/

assert.deepEqual(referencedVars(parseL3("(lambda (y) (lambda (z) x))")), [makeVarRef("x")]);
assert.deepEqual(referencedVars(parseL3("(+ x y)")), [makeVarRef("x"), makeVarRef("y")]);
assert.deepEqual(referencedVars(parseL3("(if x 1 2)")), [makeVarRef("x")]);
assert.deepEqual(referencedVars(parseL3("(plus x 1)")), [makeVarRef("plus"), makeVarRef("x")]);


