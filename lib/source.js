import { WeakStackFrame } from '@bablr/weak-stack';
import { maybeWait, getStreamIterator, emptyStreamIterator } from '@bablr/agast-helpers/stream';
import { facades, actuals } from './facades.js';

// Queue item instances are shared between all forks.
class QueueItem {
  constructor(step) {
    this.step = step;
    this.next = null;
  }
}

class Exchange {
  constructor(iterator) {
    if (!iterator) throw new Error();

    this.iterator = iterator;
    this.tail = new QueueItem(null);
    this.head = this.tail;
    this.forks = 0;
  }

  static from(iterable) {
    return new Exchange(getStreamIterator(iterable));
  }

  get isWaiting() {
    return this.head.step instanceof Promise;
  }

  allocateFork(fork) {
    const { head = this.tail, exchange = this, current } = fork || {};
    ++this.forks;
    return new Fork(head, exchange, current);
  }

  advance() {
    this.tail = this.tail.next;
  }

  fetch() {
    let step = this.iterator.next();

    if (step instanceof Promise) {
      step = step.then((step) => {
        newItem.step = step;
        return step;
      });
    }

    let newItem = new QueueItem(step);

    this.head.next = newItem;
    this.head = this.head.next;

    return newItem;
  }

  releaseFork(fork) {
    --this.forks;
    if (this.forks === 0) {
      this.iterator.return?.();
    }
    return { value: undefined, done: true };
  }
}

class ForkIterator {
  constructor(fork) {
    facades.set(fork.clone(), this);
  }

  next() {
    const fork = actuals.get(this);
    if (!fork.done) {
      const { head } = fork;
      fork.advance();
      return maybeWait(fork.head.step, () => head.step);
    } else {
      return { value: undefined, done: true };
    }
  }

  return() {
    actuals.get(this).return();
    return { value: undefined, done: true };
  }

  [Symbol.for('@@streamIterator')]() {
    return this;
  }
}

class Fork {
  constructor(head, exchange, done = false) {
    this.head = head; // QueueItem
    this.exchange = exchange;
    this._done = done;
  }

  get done() {
    return this._done || this.head.step?.done;
  }

  get value() {
    return this.done ? { value: undefined, done: true } : this.head.step?.value;
  }

  advance() {
    const { exchange } = this;

    if (this.done) {
      throw new Error('cannot advance a fork that is done');
    } else {
      let { head } = this;

      let nextItem = this.head.next;

      if (!head.step?.done) {
        if (!nextItem) {
          nextItem = exchange.fetch();
        }

        this.head = nextItem;
      }

      return nextItem;
    }
  }

  return() {
    const { done, exchange } = this;

    if (!done) exchange.releaseFork(this);

    const step = { value: undefined, done: true };

    this._current = step;

    return step;
  }

  clone() {
    const { exchange } = this;

    return exchange.allocateFork(this);
  }

  [Symbol.for('@@streamIterator')]() {
    return new ForkIterator(this);
  }
}

export const SourceFacade = class BABLRSourceFacade {
  static from(iterable) {
    return facades.get(Source.from(iterable));
  }

  constructor(source) {
    facades.set(source, this);
  }

  [Symbol.for('@@streamIterator')]() {
    return actuals.get(this)[Symbol.for('@@streamIterator')]();
  }

  get done() {
    return actuals.get(this).done;
  }

  get value() {
    return actuals.get(this).value;
  }

  get index() {
    return actuals.get(this).index;
  }

  get atGap() {
    return actuals.get(this).atGap;
  }
};

export const Source = class BABLRSource extends WeakStackFrame {
  static from(iterable) {
    const exchange = Exchange.from(iterable);
    return Source.create(exchange.allocateFork(), exchange);
  }

  constructor(fork, exchange, index = -1, holding = false) {
    super();

    if (!fork || !exchange) throw new Error();

    this.fork = fork;
    this.exchange = exchange;
    this.index = index;
    this.holding = holding;

    new SourceFacade(this);
  }

  get value() {
    return this.holding ? null : this.fork.value;
  }

  get done() {
    return this.fork.done;
  }

  get atGap() {
    return this.holding || (!this.done && this.value == null);
  }

  advance(n = 1) {
    return new Array(n).fill(null).reduce((acc) => {
      return maybeWait(acc, () => {
        this.fork.advance();
        this.index++;
        return this.fork.step;
      });
    }, this.fork.step);
  }

  shift() {
    this.holding = true;
  }

  unshift() {
    this.holding = false;
  }

  branch() {
    const { fork, exchange, index, holding } = this;
    return this.push(exchange.allocateFork(fork), exchange, index, holding);
  }

  release() {
    this.fork.return();
  }

  accept(source) {
    this.release();
    this.fork = source.fork;
    this.index = source.index;
    this.holding = source.holding;
  }

  reject() {
    this.release();
  }

  [Symbol.for('@@streamIterator')]() {
    return this.holding ? emptyStreamIterator : this.fork.clone()[Symbol.for('@@streamIterator')]();
  }

  formatIndex() {
    return `source[${this.source.index}]`;
  }
};
