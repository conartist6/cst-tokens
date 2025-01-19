export class Pump {
  constructor() {
    this.held = null;
  }

  queue(value) {
    this.held = value;
  }

  next() {
    const { held } = this;
    if (!held) throw new Error();
    this.held = null;
    return { done: false, value: held };
  }

  [Symbol.iterator]() {
    return this;
  }
}
