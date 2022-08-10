const _ = Symbol('private');

class ContextFacade {
  constructor(context) {
    this[_] = context;
    if (context.facade) {
      throw new Error('A context can have only one facade');
    }
    context.facade = this;
  }

  get options() {
    return this[_].options;
  }

  get visitors() {
    return this[_].visitors;
  }

  get matchNodes() {
    return this[_].matchNodes;
  }
}

class Context {
  constructor(visitors, options = {}) {
    this.options = options;
    this.visitors = visitors;
    this.matchNodes = new WeakMap();

    this.facade = new ContextFacade(this);
  }
}

module.exports = { Context };