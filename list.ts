// List operations similar to car/cdr/cadr in Scheme

import { all} from 'ramda';

export const first = (x: any[]): any => x[0];
export const second = (x: any[]): any => x[1];
export const rest = (x: any[]): any[] => x.slice(1);

// A useful type predicate for homegeneous lists
export const allT = <T>(isT: (x) => x is T, x: any[]): x is T[] => all(isT, x);

