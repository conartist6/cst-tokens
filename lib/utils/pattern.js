import isString from 'iter-tools-es/methods/is-string';
import isEmpty from 'iter-tools-es/methods/is-empty';
import { generateMatches } from '@bablr/regex-vm';
import { getStreamIterator, maybeWait, printType } from '@bablr/agast-helpers/stream';
import * as l from '@bablr/agast-vm-helpers/languages';
import {
  buildAlternative,
  buildAlternatives,
  buildElements,
  buildPattern,
  buildToken,
} from '@bablr/agast-vm-helpers/builders';
import { treeFromStream } from '@bablr/agast-helpers/tree';

export const assertValidRegex = (expr) => {
  const { flags } = expr;

  if (!expr.language === 'Spamex' && expr.type === 'Regex') {
    throw new Error();
  }

  // TODO validate the rest of it
};

const buildStringRegex = (str) => {
  return buildPattern(
    buildAlternatives([
      buildAlternative(buildElements([...str].map((chr) => buildToken(l.Regex, 'Character', chr)))),
    ]),
  );
};

export const match = (pattern, source) => {
  const pattern_ = isString(pattern) ? buildStringRegex(pattern) : pattern;

  if (printType(pattern_.type) !== 'Pattern') throw new Error();

  assertValidRegex(pattern_);

  const iter = getStreamIterator(generateMatches(pattern_, source));

  const step = iter.next();

  return maybeWait(step, (step) => {
    const result = step.done ? null : step.value[0];
    return isEmpty(result) ? null : result;
  });
};

class GuardedIterator {
  constructor(pattern, source) {
    this.pattern = pattern;
    this.fork = source.fork.clone();
    this.done = false;
  }

  next() {
    const { pattern, fork } = this;

    const guardMatch = match(pattern, fork.clone());

    return maybeWait(guardMatch, (guardMatch) => {
      if (guardMatch || fork.done) {
        this.done = true;
        return { value: undefined, done: true };
      } else {
        const { value } = fork;
        return maybeWait(fork.advance(), (_) => ({ value, done: false }));
      }
    });
  }

  return() {
    this.fork.return();
  }

  [Symbol.for('@@streamIterator')]() {
    return this;
  }
}

export const guardWithPattern = (pattern, source) => {
  return new GuardedIterator(pattern, source.branch());
};
