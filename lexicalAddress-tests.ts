// ========================================================
// Lexical Address tests
import * as assert from "assert";
import { map } from 'ramda';
import { makeNumExp, makeVarDecl, makeVarRef } from "./L3-ast";
import * as la from "./lexicalAddress";

// parseLA
assert.deepEqual(la.parseLA("1"), makeNumExp(1));
assert(la.isIfExpLA(la.parseLA("(if #t (+ 1 2) 'ok)")));
assert(la.isProcExpLA(la.parseLA("(lambda (x) x)")));

// unparseLA
assert.deepEqual(la.unparseLA(la.parseLA("1")), 1);
assert.deepEqual(la.unparseLA(la.parseLA("#t")), true);
assert.deepEqual(la.unparseLA(la.parseLA("(if #t (+ 1 2) 'ok)")), ["if", true, ["+", 1, 2], ["quote", "ok"]]);
assert.deepEqual(la.unparseLA(la.parseLA("(lambda (x) x)")), ["lambda", ["x"], "x"]);
assert.deepEqual(la.unparseLA(la.parseLA("(lambda (x) (* x x))")), ["lambda", ["x"], ["*", "x", "x"]]);

// getLexicalAddress
assert.deepEqual(la.getLexicalAddress(makeVarRef("b"),
                    [la.makeLexicalAddress("a", 0, 0),
                     la.makeLexicalAddress("b", 0, 1)]),
                la.makeLexicalAddress("b", 0, 1));
assert.deepEqual(la.getLexicalAddress(makeVarRef("c"),
                [la.makeLexicalAddress("a", 0, 0),
                 la.makeLexicalAddress("b", 0, 1)]),
            la.makeFreeVar("c"));
assert.deepEqual(la.getLexicalAddress(makeVarRef("a"),
            [la.makeLexicalAddress("a", 0, 0),
             la.makeLexicalAddress("b", 0, 1),
             la.makeLexicalAddress("a", 1, 1)]),
            la.makeLexicalAddress("a", 0, 0));

// Test indexOfVar
assert.deepEqual(la.indexOfVar(makeVarDecl("b"),
                               map(makeVarDecl, ["a", "b"])),
                1);
assert.deepEqual(la.indexOfVar(makeVarDecl("c"),
                map(makeVarDecl, ["a", "b"])),
                -1);

// Test crossContour
assert.deepEqual(la.crossContour(
                        map(makeVarDecl, ["a", "b"]),
                        [la.makeLexicalAddress("a", 0, 0),
                         la.makeLexicalAddress("c", 0, 1)]),
                [la.makeLexicalAddress("a", 0, 0),
                 la.makeLexicalAddress("b", 0, 1),
                 la.makeLexicalAddress("a", 1, 0),
                 la.makeLexicalAddress("c", 1, 1)]);

const f = (s: string) => la.unparseLA(la.addLexicalAddresses(la.parseLA(s)));

assert.deepEqual(f("(lambda (x) x)"), ["lambda", ["x"], ["x", ":", 0, 0]]);
assert.deepEqual(f("(lambda (x) (lambda (y) (+ x y)))"),
    ["lambda", ["x"], ["lambda", ["y"], [["+", "free"], ["x", ":", 1, 0], ["y", ":", 0, 0]]]]);
assert.deepEqual(f("((lambda (x) (* x x)) ((lambda (x) (+ x x)) 2))"),
    [["lambda", ["x"], [["*", "free"], ["x", ":", 0, 0], ["x", ":", 0, 0]]],
     [["lambda", ["x"], [["+", "free"], ["x", ":", 0, 0], ["x", ":", 0, 0]]], 2]]);
