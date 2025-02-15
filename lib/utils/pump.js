export class Pump {
  constructor() {
    this.held = [];
  }

  queue(value) {
    this.held.push(value);
  }

  next() {
    const held = this.held[0];
    if (!held) throw new Error();
    this.held.shift();
    return { done: false, value: held };
  }

  [Symbol.iterator]() {
    return this;
  }
}
