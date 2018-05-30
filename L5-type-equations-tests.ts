// L5-type-equations-tests
import assert = require("assert");
import * as A from "./L5-ast";
import * as S from "./L5-substitution-adt";
import * as E from "./L5-type-equations";
import * as T from "./TExp";
import { isError } from "./error";

// Setup
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
    const computedType = E.inferType(e);
    const ok = T.equivalentTEs(computedType, expectedType);
    if (! ok) {
        console.log(`
Expected type ${T.unparseTExp(expectedType)}
Computed type: ${T.unparseTExp(computedType)}`);
    }
    return ok;
};

// Test solve
assert.deepEqual(E.solveEquations([E.makeEquation(T.makeTVar("T1"), T.makeTVar("T2"))]),
                 S.makeSub([T.makeTVar("T1")], [T.makeTVar("T2")]));

assert(verifyTeOfExpr("3", "number"));
assert(verifyTeOfExpr("(+ 1 2)", "number"));
assert(verifyTeOfExpr("(+ (+ 1 2) 3)", "number"));
assert(verifyTeOfExpr("+", "(number * number -> number)"));
assert(verifyTeOfExpr(">", "(number * number -> boolean)"));
assert(verifyTeOfExpr("(> 1 2)", "boolean"));
assert(verifyTeOfExpr("(> (+ 1 2) 2)", "boolean"));
assert(verifyTeOfExpr("(lambda (x) (+ x 1))", "(number -> number)"));
assert(verifyTeOfExpr("((lambda (x) (+ x 1)) 3)", "number"));
assert(verifyTeOfExpr("(lambda (x) (x 1))", "((number -> T) -> T)"));

// g: [T1->T2]
// f: [T2->T3]
// ==> (lambda(n) (f (g n)))               : [T1->T3]
// ==> (lambda(f g) (lambda(n) (f (g n)))) : [[T2-T3]*[T1->T2]->[T1->T3]]
assert(verifyTeOfExpr("(lambda (f g) (lambda (n) (f (g n))))",
                      "((T2 -> T3) * (T1 -> T2) -> (T1 -> T3))"));

// f: [N->N]
// ==> (lambda(x) (- (f 3) (f x)))             : [N->N]
// ==> (lambda(f) (lambda(x) (- (f 3) (f x)))) : [[N->N]->[N->N]]
assert(verifyTeOfExpr("(lambda (f) (lambda (x) (- (f 3) (f x))))",
                      "((number -> number) -> (number -> number))"));

assert(verifyTeOfExpr("(lambda (x) (+ (+ x 1) (+ x 1)))", "(number -> number)"));
assert(verifyTeOfExpr("(lambda () (lambda (x) (+ (+ x 1) (+ x 1))))", "(Empty -> (number -> number))"));

assert(verifyTeOfExpr("((lambda (x) (x 1 2)) +)", "number"));
assert(verifyTeOfExpr("((lambda (x) (x 1)) (lambda (y) y))", "number"));

// Circular types cannot be inferred
assert(verifyTeOfExpr("(lambda (x) (x x))", "T"));

// A free variable cannot have type inferred
assert(verifyTeOfExpr("x", "T"));

// A free variable whose type is inferred from context
assert(verifyTeOfExpr("(+ x 1)", "number"));

// Not enough info in context to infer type of f
assert(verifyTeOfExpr("(f 1)", "T"));

// Primitive provides sufficient info
assert(verifyTeOfExpr("(> (f 1) 0)", "boolean"));

// Parameters that are not used
assert(verifyTeOfExpr("(lambda (x) 1)", "(T -> number)"));
assert(verifyTeOfExpr("(lambda (x y) x)", "(T1 * T2 -> T1)"));
assert(verifyTeOfExpr("((lambda (x) 1) 2)", "number"));

// Bad number of parameters
// Extra param
assert(verifyTeOfExpr("((lambda () 1) 2)", "Error"));
// Missing param
assert(verifyTeOfExpr("((lambda (x) 1))", "Error"));
