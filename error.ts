
import { all, filter, map } from "ramda";

// ========================================================
// Error handling
export const isError = (x: any): x is Error => x instanceof Error;

// Type predicate that warrants that an array does not contain errors.
// Needed for safeFL
export const hasNoError = <T1>(x: Array<T1 | Error>): x is T1[] => filter(isError, x).length === 0;
export const getErrorMessages = (x: any[]): string =>
    map((x) => JSON.stringify(x.message), filter(isError, x)).join("\n");

// Make a safe version of f: apply f to x but check if x is an error before applying it.
export const safeF: <T1, T2>(f: (x: T1) => T2) => (x: T1 | Error) => T2 | Error = (f) => (x) => {
    if (isError(x))
        return x;
    else
        return f(x);
}

// Same as safeF but for a function that accepts an array of values
// NOTE: we must use an annotation of the form Array<T1 | Error> instead of (T1 | Error)[]
// this is a syntactic restriction of TypeScript.
export const safeFL: <T1, T2>(f: (xs: T1[]) => T2) => (xs: Array<T1 | Error>) => T2 | Error =
    <T1, T2>(f: (xs: T1[]) => T2) =>
    (xs: Array<T1 | Error>): T2 | Error =>
        hasNoError(xs) ? f(xs) : Error(getErrorMessages(xs));

export const trust = <T>(x: T | Error): T => isError(x) ? undefined : x;